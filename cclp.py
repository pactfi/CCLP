from algosdk.transaction import StateSchema
from pyteal import (
    And,
    Assert,
    AssetHolding,
    AssetParam,
    Balance,
    Btoi,
    Bytes,
    BytesMul,
    BytesSqrt,
    Concat,
    Cond,
    Expr,
    Extract,
    Global,
    Gtxn,
    If,
    InnerTxn,
    InnerTxnBuilder,
    Int,
    Itob,
    Len,
    MinBalance,
    Not,
    OnComplete,
    Or,
    Pop,
    Return,
    ScratchVar,
    Seq,
    TealType,
    Txn,
    TxnField,
    TxnObject,
    TxnType,
)
from pytealext import (
    AutoLoadScratchVar,
    GlobalState,
    MakeInnerAssetTransferTxn,
    Min,
    MulDiv64,
    SaturatingSub,
    SerializeIntegers,
)

from .contract import Contract
from .helpers.transaction import SendToAddress, SendToCaller
from .helpers.validation import validate_algos_transfer, validate_asset_transfer

ALGOS_UNIT_NAME = "ALGO"
UNNAMED_ASSET_PLACEHOLDER = "?"
LIQUIDITY_TOKEN_NAME_SEPARATOR = "/"
LIQUIDITY_TOKEN_NAME_SUFFIX = (
    " PACT LP Token"  # the space is necessary as it's not added in contract code
)
LIQUIDITY_TOKEN_UNIT = "PLP"
LIQUIDITY_TOKEN_URL = "https://pact.fi/"
LIQUIDITY_DECIMALS = 6
LIQUIDITY_LOCK_AMOUNT = 1000  # Don't change this ever
UINT_MAX = 2**64 - 1
CONTRACT_NAME = "PACT AMM"
VERSION = 201  # 202


class ExchangeContract(Contract):
    """
    Configurable contract allowing to exchange Algos to ASA or ASA to ASA.

    For each call to the smart contract the Txn.assets must contain [primary_asset_id, secondary_asset_id]
    """

    class STATE:
        """
        String constants representing global state vars
        """

        TOTAL_LIQUIDITY = "L"
        TOTAL_PRIMARY = "A"
        TOTAL_SECONDARY = "B"
        LIQUIDITY_TOKEN_ID = "LTID"
        CONFIG = "CONFIG"
        CONTRACT_NAME = "CONTRACT_NAME"
        VERSION = "VERSION"
        ADMIN = "ADMIN"
        TREASURY = "TREASURY"
        FEE_BPS = "FEE_BPS"
        PACT_FEE_BPS = "PACT_FEE_BPS"

    class ACTIONS:
        """
        String constants representing possible actions within Pact
        """

        SWAP = "SWAP"
        ADD_LIQUIDITY = "ADDLIQ"
        REMOVE_LIQUIDITY = "REMLIQ"
        CREATE_LIQUIDITY_TOKEN = "CLT"
        OPT_IN_TO_ASSETS = "OPTIN"  # contract opt-in to assets
        WITHDRAW_FEES = "WITHDRAWFEES"
        CHANGE_ADMIN = "CHANGE_ADMIN"
        CHANGE_TREASURY = "CHANGE_TREASURY"
        CHANGE_PACT_FEE = "CHANGE_PACT_FEE"
        PARTICIPATE = "PARTICIPATE"

    def __init__(self):
        self.primary_asset_id = AutoLoadScratchVar(TealType.uint64)
        self.secondary_asset_id = AutoLoadScratchVar(TealType.uint64)

        # Set up global state vars
        self.total_liquidity = GlobalState(ExchangeContract.STATE.TOTAL_LIQUIDITY, TealType.uint64)
        self.total_primary = GlobalState(ExchangeContract.STATE.TOTAL_PRIMARY, TealType.uint64)
        self.total_secondary = GlobalState(ExchangeContract.STATE.TOTAL_SECONDARY, TealType.uint64)
        self.liquidity_token_id = GlobalState(
            ExchangeContract.STATE.LIQUIDITY_TOKEN_ID, TealType.uint64
        )
        self.amm_config = GlobalState(ExchangeContract.STATE.CONFIG, TealType.bytes)
        self.treasury_address = GlobalState(ExchangeContract.STATE.TREASURY, TealType.bytes)
        self.admin_address = GlobalState(ExchangeContract.STATE.ADMIN, TealType.bytes)
        self.contract_name = GlobalState(ExchangeContract.STATE.CONTRACT_NAME, TealType.bytes)
        self.version = GlobalState(ExchangeContract.STATE.VERSION, TealType.uint64)
        self.fee_bps = GlobalState(ExchangeContract.STATE.FEE_BPS, TealType.uint64)
        self.pact_fee_bps = GlobalState(ExchangeContract.STATE.PACT_FEE_BPS, TealType.uint64)

    def get_global_schema(self) -> StateSchema:
        num_uints = 0
        num_bytes = 0
        for k, v in vars(self).items():
            if isinstance(v, GlobalState):
                if v.type_hint == TealType.uint64:
                    num_uints += 1
                elif v.type_hint == TealType.bytes:
                    num_bytes += 1
                else:
                    raise AttributeError(f"{k} (GlobalState) doesn't have specified type hint")
        return StateSchema(num_uints, num_bytes)

    def get_local_schema(self) -> StateSchema:
        return StateSchema(0, 0)

    def _validate_common_txn_fields(self) -> Expr:
        """
        Check if some common expectations about Txn are valid:
        - Txn.assets is of size at most 3 and contains the primary asset id, secondary asset id and optionally the liquidity asset id
        - Txn.rekey_to() is zero address
        - OnComplete must be NoOp
        These must be true with every interaction with the contract.
        """
        return And(
            Txn.rekey_to() == Global.zero_address(),
            Txn.assets[0] == self.primary_asset_id,
            Txn.assets[1] == self.secondary_asset_id,
            # don't allow more assets than expected, also if there is a third asset it must be the liquidity token ID
            Txn.assets.length() <= Int(3),
            If(Txn.assets.length() == Int(3))
            .Then(Txn.assets[2] == self.liquidity_token_id.get())
            .Else(Int(1)),  # Txn assets length < 3, no need to check index 2
            Txn.on_completion()
            == OnComplete.NoOp,  # no opt in, no closeout, no updating, no deleting
        )

    def get_program(self) -> Expr:
        config = AutoLoadScratchVar(TealType.bytes)

        return Seq(
            If(Txn.application_id())
            .Then(
                config.store(self.amm_config.get()),
                self.primary_asset_id.store(Btoi(Extract(config, Int(0), Int(8)))),
                self.secondary_asset_id.store(Btoi(Extract(config, Int(8), Int(8)))),
                Assert(self._validate_common_txn_fields()),
                self.on_noop(),
            )
            .Else(
                Assert(Txn.on_completion() == OnComplete.NoOp),
                self.on_create(),
            )
        )

    def on_noop(self) -> Expr:
        return Cond(
            # Config
            [
                Txn.application_args[0] == Bytes(ExchangeContract.ACTIONS.OPT_IN_TO_ASSETS),
                self.on_opt_in_to_assets(),
            ],
            [
                Txn.application_args[0] == Bytes(ExchangeContract.ACTIONS.CREATE_LIQUIDITY_TOKEN),
                self.on_create_liquidity_token(),
            ],
            # User actions
            [Txn.application_args[0] == Bytes(ExchangeContract.ACTIONS.SWAP), self.on_swap()],
            [
                Txn.application_args[0] == Bytes(ExchangeContract.ACTIONS.ADD_LIQUIDITY),
                self.on_add_liquidity(),
            ],
            [
                Txn.application_args[0] == Bytes(ExchangeContract.ACTIONS.REMOVE_LIQUIDITY),
                self.on_remove_liquidity(),
            ],
            [
                Txn.application_args[0] == Bytes(ExchangeContract.ACTIONS.WITHDRAW_FEES),
                self.on_withdraw_fees(),
            ],
            # Admin actions
            [
                Txn.application_args[0] == Bytes(ExchangeContract.ACTIONS.CHANGE_ADMIN),
                self.on_change_admin(),
            ],
            [
                Txn.application_args[0] == Bytes(ExchangeContract.ACTIONS.CHANGE_TREASURY),
                self.on_change_treasury(),
            ],
            [
                Txn.application_args[0] == Bytes(ExchangeContract.ACTIONS.CHANGE_PACT_FEE),
                self.on_change_pact_fee(),
            ],
            # Other actions
            [
                Txn.application_args[0] == Bytes(ExchangeContract.ACTIONS.PARTICIPATE),
                self.on_participate(),
            ],
        )

    def get_clear_program(self) -> Expr:
        # There is not much that should happen when someone clears state
        return Int(1)

    def _is_algos_exchange(self) -> Expr:
        """
        Returns:
            Expression evaluating to 1 iff the exchange is an Algos to ASA exchange (0 otherwise)
        """
        return Not(self.primary_asset_id)

    def _validate_primary_asset_deposit(self, txn: TxnObject) -> Expr:
        """
        Check if the provided transaction is a valid deposit.
        If it's an algos exchange - check Algo deposit, otherwise check asset deposit

        Returns:
            Boolean Expression checking if the deposit transfer is correct
        """
        return If(
            self._is_algos_exchange(),
            validate_algos_transfer(txn, receiver=Global.current_application_address()),
            validate_asset_transfer(
                txn, asset_id=self.primary_asset_id, receiver=Global.current_application_address()
            ),
        )

    def _validate_secondary_asset_deposit(self, txn: TxnObject) -> Expr:
        """
        Check if the provided transaction is a valid secondary asset deposit.
        """
        return validate_asset_transfer(
            txn, asset_id=self.secondary_asset_id, receiver=Global.current_application_address()
        )

    def _validate_liquidity_deposit(self, txn: TxnObject) -> Expr:
        """
        Check whether the provided txn is a valid liquidity token deposit
        """
        return validate_asset_transfer(
            txn,
            asset_id=self.liquidity_token_id.get(),
            receiver=Global.current_application_address(),
        )

    def _primary_asset_transfer_amount(self, txn: TxnObject) -> Expr:
        """
        Returns an expression evaluating to the amount of primary asset transferred in a given txn

        If Algos are exchanged on this exchange the "amount" field of the txn is returned, otherwise the "asset_amount" field is returned.
        """
        return If(self._is_algos_exchange(), txn.amount(), txn.asset_amount())

    def _secondary_asset_transfer_amount(self, txn: TxnObject) -> Expr:
        """
        Returns an expression evaluating to amount of transferred secondary asset
        """
        return txn.asset_amount()

    def _liquidity_transfer_amount(self, txn: TxnObject) -> Expr:
        """
        Returns an expression evaluating to amount of transferred liquidity asset
        """
        return txn.asset_amount()

    def on_create(self) -> Seq:
        """
        Initialize global variables
        Create liquidity token

        Txn.args:
            [0] - fee bps
            [1] - pact fee bps
            [2] - admin address
            [3] - treasury address

        Txn.assets:
            [0] - primary asset id
            [1] - secondary asset id
        """
        primary_asset = Txn.assets[0]
        secondary_asset = Txn.assets[1]
        fee_bps = Btoi(Txn.application_args[0])
        pact_fee_bps = Btoi(Txn.application_args[1])
        admin_address = Txn.application_args[2]
        treasury_address = Txn.application_args[3]
        return Seq(
            # prevent malformed contracts from being created on-chain
            # this are the same checks that we do in __init__
            Assert(
                primary_asset < secondary_asset,
                comment="Primary asset ID must be less than secondary asset ID",
            ),
            Assert(fee_bps < Int(10000), comment="Exchange fee must be less than 10000"),
            Assert(
                pact_fee_bps <= fee_bps / Int(2),
                comment="Pact fee must be less than half of the exchange fee",
            ),
            Assert(
                Or(pact_fee_bps, Int(LIQUIDITY_LOCK_AMOUNT)),
                comment="There must be one source of protection against LP price inflation attack",
            ),
            Assert(
                Len(admin_address) == Int(32),
                comment="Admin address must be 32 bytes long",
            ),
            Assert(
                Len(treasury_address) == Int(32),
                comment="Treasury address must be 32 bytes long",
            ),
            # set the defaults for the global state variables
            self.amm_config.put(SerializeIntegers(primary_asset, secondary_asset, fee_bps)),
            self.contract_name.put(Bytes(CONTRACT_NAME)),
            self.version.put(Int(VERSION)),
            self.total_primary.put(Int(0)),
            self.total_secondary.put(Int(0)),
            self.total_liquidity.put(Int(0)),
            self.liquidity_token_id.put(Int(0)),
            self.admin_address.put(admin_address),
            self.treasury_address.put(treasury_address),
            self.fee_bps.put(fee_bps),
            self.pact_fee_bps.put(pact_fee_bps),
            Return(Int(1)),
        )

    def on_opt_in_to_assets(self) -> Seq:
        """
        Opt in to primary (if not algos) and secondary assets.
        Can only be executed by the creator

        Itxns: 1-2
        """
        return Seq(
            Assert(Txn.sender() == Global.creator_address()),
            If(Not(self._is_algos_exchange())).Then(
                MakeInnerAssetTransferTxn(
                    asset_receiver=Global.current_application_address(),
                    asset_amount=Int(0),
                    xfer_asset=self.primary_asset_id,
                    fee=Int(0),  # must be pooled
                )
            ),
            MakeInnerAssetTransferTxn(
                asset_receiver=Global.current_application_address(),
                asset_amount=Int(0),
                xfer_asset=self.secondary_asset_id,
                fee=Int(0),  # must be pooled
            ),
            Return(Int(1)),
        )

    def on_create_liquidity_token(self) -> Seq:
        """
        Create liquidity token for use with the exchange
        Can only be done once. Only the creator can execute this action.

        Txn.assets:
            [0]: Primary asset ID (in case it's an algos exchange, this has to be set to 0)
            [1]: Secondary asset ID

        Itxns: 1
        """
        primary_unit = ScratchVar(TealType.bytes)
        secondary_unit = ScratchVar(TealType.bytes)

        ap_primary_unit_name = AssetParam.unitName(self.primary_asset_id)
        ap_secondary_unit_name = AssetParam.unitName(self.secondary_asset_id)

        # liquidity token's name will be in format "UNIT1/UNIT2 liquidity"
        liquidity_token_name = Concat(
            primary_unit.load(),
            Bytes(LIQUIDITY_TOKEN_NAME_SEPARATOR),
            secondary_unit.load(),
            Bytes(LIQUIDITY_TOKEN_NAME_SUFFIX),
        )
        liquidity_token_unit = Bytes(LIQUIDITY_TOKEN_UNIT)
        liquidity_token_url = Bytes(LIQUIDITY_TOKEN_URL)
        return Seq(
            # Only the creator can execute this action
            Assert(Txn.sender() == Global.creator_address()),
            # make sure the liquidity token doesn't exist yet
            Assert(self.liquidity_token_id.get() == Int(0)),
            If(self._is_algos_exchange())
            .Then(
                # Primary unit name is "ALGO"
                primary_unit.store(Bytes(ALGOS_UNIT_NAME))
            )
            .Else(
                # It's an ASA to ASA exchange - load asset's unit name from the blockchain
                Seq(
                    ap_primary_unit_name,  # eval MaybeValue
                    If(ap_primary_unit_name.value() == Bytes(""))
                    .Then(
                        # Empty asset unitname, therefore set default
                        primary_unit.store(Bytes(UNNAMED_ASSET_PLACEHOLDER))
                    )
                    .Else(primary_unit.store(ap_primary_unit_name.value())),
                )
            ),
            ap_secondary_unit_name,  # eval MaybeValue
            If(ap_secondary_unit_name.value() == Bytes(""))
            .Then(
                # Secondary asset's unit name empty, so set a default
                secondary_unit.store(Bytes(UNNAMED_ASSET_PLACEHOLDER))
            )
            .Else(
                # Secondary asset's unit name found
                secondary_unit.store(ap_secondary_unit_name.value())
            ),
            # The fetched unit names are stored in slots and accesed through liquidity_token_name expr
            # Execute the asset create txn
            InnerTxnBuilder.Begin(),
            InnerTxnBuilder.SetFields(
                {
                    TxnField.fee: Int(0),  # must be pooled
                    TxnField.type_enum: TxnType.AssetConfig,
                    TxnField.config_asset_total: Int(UINT_MAX),
                    TxnField.config_asset_decimals: Int(LIQUIDITY_DECIMALS),
                    TxnField.config_asset_name: liquidity_token_name,
                    TxnField.config_asset_unit_name: liquidity_token_unit,
                    TxnField.config_asset_url: liquidity_token_url,
                    TxnField.config_asset_reserve: Global.current_application_address(),
                }
            ),
            InnerTxnBuilder.Submit(),
            self.liquidity_token_id.put(InnerTxn.created_asset_id()),
            Return(Int(1)),
        )

    def on_swap(self) -> Seq:
        """
        Swap assets for other assets, auto-detect which asset is being deposited.

        Gtxn specification:
            [i-1]: valid deposit in primary asset or secondary asset
            [i] (Txn): current application call

        Expected Txn.application_args:
            [0]: ACTION.SWAP (implied)
            [1]: expected minimum of the other token to receive from swap (prevent slippage)
        """
        deposit_txn = Gtxn[Txn.group_index() - Int(1)]
        min_expected = Btoi(Txn.application_args[1])
        return Seq(
            # check if primary asset is being deposited and the deposit is correct
            If(self._validate_primary_asset_deposit(deposit_txn))
            .Then(
                self._swap_primary(self._primary_asset_transfer_amount(deposit_txn), min_expected)
            )
            .ElseIf(self._validate_secondary_asset_deposit(deposit_txn))
            .Then(
                self._swap_secondary(
                    self._secondary_asset_transfer_amount(deposit_txn), min_expected
                )
            )
            .Else(Return(Int(0))),  # no valid deposit was made in the next transaction in a group
            Return(Int(1)),
        )

    def on_add_liquidity(self) -> Seq:
        """
        User adds liquidity to the exchange.
        Initially, if there is no liquidity in the pool they should receive a geometric mean (sqrt(a*b)) liquidity tokens.
        Otherwise the received liquidity tokens should be proportionate to the deposited amount min(a/A*LT, b/B*LT).
        The unused tokens sent in a deposit are sent back to the user via inner txn.
        The received liquidity tokens are sent back to the user.
        If the received amount of liquidity tokens is smaller than the user expects, the transaction fails.

        Gtxn spec:
            [i-2]: Primary asset deposit
            [i-1]: Secondary asset deposit
            [i] (Txn): This application call

        Txn.application_args:
            [0]: ACTION.ADD_LIQUIDITY (implied)
            [1]: minimum expected liquidity tokens (the minimum accepted amount of liquidity tokens that the user will receive)

        Itxns: 1-2
        """
        min_expected = Btoi(Txn.application_args[1])
        primary_deposit_txn = Gtxn[Txn.group_index() - Int(2)]
        secondary_deposit_txn = Gtxn[Txn.group_index() - Int(1)]
        primary_deposit_amount = self._primary_asset_transfer_amount(primary_deposit_txn)
        secondary_deposit_amount = self._secondary_asset_transfer_amount(secondary_deposit_txn)

        lt_primary = ScratchVar()
        lt_secondary = ScratchVar()
        lt_minted = ScratchVar()

        # auxiliary variable to calculate primary amount refund
        previous_total_primary = ScratchVar()
        # auxiliary variable to calculate secondary amount refund
        previous_total_secondary = ScratchVar()

        remaining_primary = ScratchVar()  # amount of primary asset remaining after deposit
        remaining_secondary = ScratchVar()  # amount of secondary asset reaining after deposit
        return Seq(
            Assert(self.liquidity_token_id.get()),
            Assert(self._validate_primary_asset_deposit(primary_deposit_txn)),
            Assert(self._validate_secondary_asset_deposit(secondary_deposit_txn)),
            If(self.total_liquidity.get() == Int(0))
            .Then(
                # Initial liquidity
                Seq(
                    lt_minted.store(
                        Btoi(
                            BytesSqrt(
                                BytesMul(
                                    Itob(primary_deposit_amount), Itob(secondary_deposit_amount)
                                )
                            )
                        )
                    ),
                    # Amount is stored in global state without modifications
                    self.total_liquidity.put(lt_minted.load()),
                    self.total_primary.put(primary_deposit_amount),
                    self.total_secondary.put(secondary_deposit_amount),
                    # Lock the tokens
                    lt_minted.store(lt_minted.load() - Int(LIQUIDITY_LOCK_AMOUNT)),
                    # Check if there are enough tokens and send the liquidity tokens to the caller
                    Assert(lt_minted.load() >= min_expected),
                    SendToCaller(self.liquidity_token_id.get(), lt_minted.load()),
                )
            )
            .Else(
                # There is some liquidity already present
                # Calculate the proportion of deposited amount to total tokens present in the pool
                Seq(
                    # calculate lt_a = a/A * LT (how many liquidity tokens the sender deserves based on his primary deposit)
                    lt_primary.store(
                        MulDiv64(
                            primary_deposit_amount,
                            self.total_liquidity.get(),
                            self.total_primary.get(),
                        )
                    ),
                    # calculate lt_b = b/B * LT (how many liquidity tokens the sender deserves based on his secondary deposit)
                    lt_secondary.store(
                        MulDiv64(
                            secondary_deposit_amount,
                            self.total_liquidity.get(),
                            self.total_secondary.get(),
                        )
                    ),
                    # make sure that the user receives at least {min_expected} liquidity tokens
                    # use underflow on subtraction as an error to better recognize this error on the frontend
                    Pop(Min(lt_primary.load(), lt_secondary.load()) - min_expected),
                    # terminate the execution if no tokens were minted
                    Assert(Min(lt_primary.load(), lt_secondary.load()) > Int(0)),
                    # Immediatelly send the liquidity tokens to the sender
                    SendToCaller(
                        self.liquidity_token_id.get(), Min(lt_primary.load(), lt_secondary.load())
                    ),
                    # save the added liquidity L' = L + min(a/A * L, b/B * L)
                    self.total_liquidity.add_assign(Min(lt_primary.load(), lt_secondary.load())),
                    If(lt_primary.load() > lt_secondary.load())
                    .Then(
                        Seq(
                            previous_total_primary.store(self.total_primary.get()),
                            # add the amount of primary asset to the pool based on ratio of secondary asset added
                            # A' = ceil(b/B * A) + A, ceil ensures that refund won't be negative as it might happen with floor(b/B * A) + A + 1
                            self.total_primary.add_assign(
                                MulDiv64(
                                    secondary_deposit_amount,
                                    self.total_primary.get(),
                                    self.total_secondary.get(),
                                    ceiling=True,
                                )
                            ),
                            # calculate refund - unused secondary amount to mint total secondary
                            remaining_primary.store(
                                primary_deposit_amount
                                - (self.total_primary.get() - previous_total_primary.load())
                            ),
                            SendToCaller(self.primary_asset_id, remaining_primary.load()),
                            self.total_secondary.add_assign(secondary_deposit_amount),
                        )
                    )
                    .ElseIf(lt_primary.load() < lt_secondary.load())
                    .Then(
                        Seq(
                            previous_total_secondary.store(self.total_secondary.get()),
                            # add the amount of secondary asset to the pool based on ratio of primary asset added
                            # B' = ceil(a/A * B) + B, ceil ensures that refund won't be negative as it might happen with floor(a/A * B) + B + 1
                            self.total_secondary.add_assign(
                                MulDiv64(
                                    primary_deposit_amount,
                                    self.total_secondary.get(),
                                    self.total_primary.get(),
                                    ceiling=True,
                                )
                            ),
                            # calculate refund - unused secondary amount to mint total secondary
                            remaining_secondary.store(
                                secondary_deposit_amount
                                - (self.total_secondary.get() - previous_total_secondary.load())
                            ),
                            # return the refund back to sender
                            SendToCaller(self.secondary_asset_id, remaining_secondary.load()),
                            self.total_primary.add_assign(primary_deposit_amount),
                        )
                    )
                    .Else(
                        # special case: lt_primary == lt_secondary
                        # we cannot easily tell on which side should the tokens be refunded
                        # therefore, all are donated to the pool
                        Seq(
                            self.total_primary.add_assign(primary_deposit_amount),
                            self.total_secondary.add_assign(secondary_deposit_amount),
                        )
                    ),
                )
            ),
            Return(Int(1)),
        )

    def on_remove_liquidity(self) -> Seq:
        """
        User removes liquidity from the pool.
        This is done by depositing liquidity tokens, the contract sends back primary and secondary asset
        proportional to how many tokens are contained in the pool.
        The tokens are sent back via inner transactions.

        Gtxn spec:
            [i-1]: liquidity asset deposit
            [i] (Txn): Application call currently executing

        Txn.application_args:
            [0]: ACTION.REMOVE_LIQUIDITY (implied)
            [1]: minimum expected primary asset (the minimum accepted amount of primary asset that the user will receive)
            [2]: minimum expected secondary asset (the minimum accepted amount of secondary asset that the user will receive)
        """
        liquidity_deposit_txn = Gtxn[Txn.group_index() - Int(1)]
        min_expected_primary = Btoi(Txn.application_args[1])
        min_expected_secondary = Btoi(Txn.application_args[2])
        liquidity_deposit_amount = self._liquidity_transfer_amount(liquidity_deposit_txn)

        primary_amount = ScratchVar()  # amount of primary asset to be returned
        secondary_amount = ScratchVar()  # amount of secondary asset to be returned

        return Seq(
            Assert(self._validate_liquidity_deposit(liquidity_deposit_txn)),
            Assert(self.total_liquidity.get() != Int(0)),
            #  calculate how much of primary and secondary should be sent based on liquidity
            primary_amount.store(
                MulDiv64(
                    liquidity_deposit_amount, self.total_primary.get(), self.total_liquidity.get()
                )
            ),
            secondary_amount.store(
                MulDiv64(
                    liquidity_deposit_amount, self.total_secondary.get(), self.total_liquidity.get()
                )
            ),
            # remove liquidity and returned assets from global state
            self.total_primary.sub_assign(primary_amount.load()),
            self.total_secondary.sub_assign(secondary_amount.load()),
            self.total_liquidity.sub_assign(liquidity_deposit_amount),
            # check if both amount are bigger than minimal expected
            Pop(secondary_amount.load() - min_expected_secondary),
            Pop(primary_amount.load() - min_expected_primary),
            SendToCaller(self.primary_asset_id, primary_amount.load()),
            SendToCaller(self.secondary_asset_id, secondary_amount.load()),
            Return(Int(1)),
        )

    def on_withdraw_fees(self) -> Seq:
        """
        Withdraw to treasury all accrued fees and wild deposits into the contract account.
        """
        ah_primary = AssetHolding.balance(
            Global.current_application_address(), self.primary_asset_id
        )
        ah_secondary = AssetHolding.balance(
            Global.current_application_address(), self.secondary_asset_id
        )
        algo_balance = Balance(Global.current_application_address()) - MinBalance(
            Global.current_application_address()
        )
        primary_balance = If(
            self.primary_asset_id, Seq(ah_primary, ah_primary.value()), algo_balance
        )
        secondary_balance = Seq(ah_secondary, ah_secondary.value())

        # Saturating at 0 allows withdrawing fees in case the pool is insolvent in one currency
        surplus_primary = SaturatingSub(primary_balance, self.total_primary.get())
        surplus_secondary = SaturatingSub(secondary_balance, self.total_secondary.get())
        return Seq(
            # make reserves match with global state
            # by setting the fees to the surplus value
            SendToAddress(
                self.treasury_address.get(),
                self.primary_asset_id,
                surplus_primary,
            ),
            SendToAddress(
                self.treasury_address.get(),
                self.secondary_asset_id,
                surplus_secondary,
            ),
            # Withdraw surplus algos in non-algo exchange
            If(
                self.primary_asset_id,
                SendToAddress(
                    self.treasury_address.get(),
                    Int(0),
                    algo_balance,
                ),
            ),
            Return(Int(1)),
        )

    def on_change_admin(self) -> Seq:
        """
        Change the admin address, the new admin has to be set through Txn.accounts.
        """
        new_admin = Txn.accounts[1]
        return Seq(
            Assert(Txn.sender() == self.admin_address.get()),
            Assert(Len(new_admin) == Int(32)),
            self.admin_address.put(new_admin),
            Return(Int(1)),
        )

    def on_change_treasury(self) -> Seq:
        """
        Change the treasury address, the new treasury has to be set through Txn.accounts.
        """
        new_treasury = Txn.accounts[1]
        return Seq(
            Assert(Txn.sender() == self.admin_address.get()),
            Assert(Len(new_treasury) == Int(32)),
            self.treasury_address.put(new_treasury),
            Return(Int(1)),
        )

    def on_change_pact_fee(self) -> Seq:
        """
        Change the pact fee, the new pact fee has to be set through Txn.application_args.
        The new fee must be in basis points.
        """
        new_pact_fee = Btoi(Txn.application_args[1])
        return Seq(
            Assert(Txn.sender() == self.admin_address.get()),
            Assert(new_pact_fee <= self.fee_bps.get() / Int(2)),
            self.pact_fee_bps.put(new_pact_fee),
            Return(Int(1)),
        )

    def on_participate(self) -> Seq:
        """
        Update participation
        Args:
            [1] - votFirst
            [2] - votLast
            [3] - votKeyDilution
            [4] - selKey
            [5] - votKey
            [6] - spKey
        """
        votFirst = Btoi(Txn.application_args[1])
        votLast = Btoi(Txn.application_args[2])
        votKeyDilution = Btoi(Txn.application_args[3])
        selKey = Txn.application_args[4]
        votKey = Txn.application_args[5]
        spKey = Txn.application_args[6]
        algo_payment_index = Txn.group_index() - Int(1)
        algo_payment_txn = Gtxn[algo_payment_index]
        algo_payment_amount = algo_payment_txn.amount()
        return Seq(
            Assert(Txn.sender() == self.treasury_address.get()),
            # validate algo payment
            Assert(
                And(
                    algo_payment_txn.type_enum() == TxnType.Payment,
                    algo_payment_txn.receiver() == Global.current_application_address(),
                    algo_payment_amount >= Int(1000),  # require min txn fee amount
                ),
                comment="Must include 2 ALGO payment to application",
            ),
            Assert(
                Len(selKey) == Int(32),
                comment="Selection public key must be 32 bytes long",
            ),
            Assert(
                Len(votKey) == Int(32),
                comment="Vote public key must be 32 bytes long",
            ),
            Assert(
                Len(spKey) == Int(64),
                comment="State proof public key must be 64 bytes long",
            ),
            InnerTxnBuilder.Begin(),
            InnerTxnBuilder.SetFields(
                {
                    TxnField.type_enum: TxnType.KeyRegistration,
                    TxnField.vote_pk: votKey,
                    TxnField.selection_pk: selKey,
                    TxnField.vote_first: votFirst,
                    TxnField.vote_last: votLast,
                    TxnField.vote_key_dilution: votKeyDilution,
                    TxnField.state_proof_pk: spKey,
                    TxnField.fee: algo_payment_amount,
                }
            ),
            InnerTxnBuilder.Submit(),
            Return(Int(1)),
        )

    def _swap_primary(self, amount: Expr, min_expected: Expr) -> Expr:
        """
        Swap `amount` of primary asset into secondary asset and send the received secondary asset to the user.
        Checks that the amount received from swap is at least `min_expected` (to prevent slippage)
        """
        taxed_secondary_amount = ScratchVar()
        secondary_amount = ScratchVar()
        pact_fee_amt = ScratchVar()
        return Seq(
            secondary_amount.store(
                MulDiv64(amount, self.total_secondary.get(), self.total_primary.get() + amount)
            ),
            pact_fee_amt.store(
                MulDiv64(secondary_amount.load(), self.pact_fee_bps.get(), Int(10000))
            ),
            taxed_secondary_amount.store(
                MulDiv64(secondary_amount.load(), (Int(10000) - self.fee_bps.get()), Int(10000))
            ),
            # check if slippage is not to large
            Pop(taxed_secondary_amount.load() - min_expected),
            self.total_secondary.sub_assign(taxed_secondary_amount.load()),
            self.total_secondary.sub_assign(pact_fee_amt.load()),
            self.total_primary.add_assign(amount),
            SendToCaller(self.secondary_asset_id, taxed_secondary_amount.load()),
            Return(Int(1)),
        )

    def _swap_secondary(self, amount: Expr, min_expected: Expr) -> Expr:
        """
        Swap `amount` of secondary asset into primary asset and send the received primary asset to the user.
        Checks that the amount received from swap is at least `min_expected` (to prevent slippage)
        """
        primary_amount = ScratchVar()
        taxed_primary_amount = ScratchVar()
        pact_fee_amt = ScratchVar()
        return Seq(
            primary_amount.store(
                MulDiv64(amount, self.total_primary.get(), self.total_secondary.get() + amount)
            ),
            pact_fee_amt.store(
                MulDiv64(primary_amount.load(), self.pact_fee_bps.get(), Int(10000))
            ),
            taxed_primary_amount.store(
                MulDiv64(primary_amount.load(), (Int(10000) - self.fee_bps.get()), Int(10000))
            ),
            # check if slippage is not to large
            Pop(taxed_primary_amount.load() - min_expected),
            self.total_primary.sub_assign(taxed_primary_amount.load()),
            self.total_primary.sub_assign(pact_fee_amt.load()),
            self.total_secondary.add_assign(amount),
            SendToCaller(self.primary_asset_id, taxed_primary_amount.load()),
            Return(Int(1)),
        )
