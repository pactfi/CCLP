from pyteal import (
    Bytes,
    Expr,
    Gtxn,
    If,
    InnerTxnBuilder,
    Int,
    OnComplete,
    Seq,
    Subroutine,
    TealType,
    Txn,
    TxnType,
)
from pytealext import (
    InnerAssetTransferTxn,
    InnerPaymentTxn,
    MakeInnerApplicationCallTxn,
    MakeInnerAssetTransferTxn,
    MakeInnerPaymentTxn,
)
from pytealext.inner_transactions import InnerTxn

# Approval Program for the dummy app that will be used to boost opcode budget
# The TEAL code used to construct this program is:
# #pragma version 7
# pushint 1
DUMMY_APPROVAL_PROGRAM = "B4EB"


@Subroutine(TealType.none)
def increase_opcode_quota() -> Expr:
    """
    Increases the opcode quota of the currently running app call by roughly 690.
    """

    return MakeInnerApplicationCallTxn(
        approval_program=Bytes("base64", DUMMY_APPROVAL_PROGRAM),
        # Clear state doesn't matter, so we'll just use the same program
        clear_state_program=Bytes("base64", DUMMY_APPROVAL_PROGRAM),
        on_completion=OnComplete.DeleteApplication,
        fee=Int(0),
    )


@Subroutine(TealType.none)
def SendToCaller(asset_id: Expr, amount: Expr) -> Expr:
    """
    Send {amount} of {asset_id} to Txn.sender().

    If {asset_id} is 0, then send {amount} microAlgos to Txn.sender() instead.

    The fees are set to 0 to prevent the SSC from burning throug it's Algos.
    Therefore they must be pooled
    """
    return If(
        asset_id,  # check if it's an asset transfer (asset_id > 0)
        MakeInnerAssetTransferTxn(  # transfer the asset from SSC controlled address to caller
            asset_receiver=Txn.sender(), asset_amount=amount, xfer_asset=asset_id, fee=Int(0)
        ),
        MakeInnerPaymentTxn(  # transfer algos from SSC controlled address to the caller
            receiver=Txn.sender(), amount=amount, fee=Int(0)
        ),
    )


@Subroutine(TealType.none)
def SendToAddress(address: Expr, asset_id: Expr, amount: Expr) -> Expr:
    """
    TODO: remove (superseded by MakeInnerTransferTxn)

    Generalized version of SendToCaller, where the address can be set explicitly.

    Send {amount} of {asset_id} to {address}.

    If {asset_id} is 0, then send {amount} microAlgos to {address} instead.

    The fees are set to 0 to prevent the SSC from burning through its Algos.
    Therefore they must be pooled
    """
    return If(
        asset_id,  # check if it's an asset transfer (asset_id > 0)
        MakeInnerAssetTransferTxn(  # transfer the asset from SSC controlled address to the address
            asset_receiver=address, asset_amount=amount, xfer_asset=asset_id, fee=Int(0)
        ),
        MakeInnerPaymentTxn(  # transfer algos from SSC controlled address to the address
            receiver=address, amount=amount, fee=Int(0)
        ),
    )


@Subroutine(TealType.uint64)
def get_deposited_amount(txn_index: Expr) -> Expr:
    """Get the amount of the deposited asset or deposited algos

    Args:
        txn_index: The transaction number in the group.
    """
    deposit_txn = Gtxn[txn_index]
    return If(
        deposit_txn.type_enum() == TxnType.Payment, deposit_txn.amount(), deposit_txn.asset_amount()
    )


@Subroutine(TealType.uint64)
def get_deposited_asset_id(txn_index: Expr) -> Expr:
    """Get the asset ID of the deposited asset or 0 if algos were deposited

    Args:
        txn_index: The transaction number in the group.
    """
    deposit_txn = Gtxn[txn_index]
    return If(deposit_txn.type_enum() == TxnType.Payment, Int(0), deposit_txn.xfer_asset())


@Subroutine(TealType.none)
def _inner_transfer_txn(receiver: Expr, amount: Expr, asset_id: Expr):
    """Cached in a subroutine to avoid TEAL code duplication"""
    return If(
        asset_id,
        InnerAssetTransferTxn(
            asset_receiver=receiver, asset_amount=amount, xfer_asset=asset_id, fee=Int(0)
        ),
        InnerPaymentTxn(receiver=receiver, amount=amount, fee=Int(0)),
    )


class InnerTransferTxn(InnerTxn):
    """Inner transfer that handles both ASAs and Algos"""

    def __init__(self, receiver: Expr, amount: Expr, asset_id: Expr):
        super().__init__()

        self.expr = _inner_transfer_txn(receiver, amount, asset_id)


def MakeInnerTransferTxn(
    receiver: Expr,
    amount: Expr,
    asset_id: Expr,
):
    """Execute an inner transfer that handles both ASAs and Algos"""
    return Seq(
        InnerTxnBuilder.Begin(),
        InnerTransferTxn(receiver, amount, asset_id),
        InnerTxnBuilder.Submit(),
    )
