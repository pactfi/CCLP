from typing import Optional

from pyteal import (
    And,
    Assert,
    Expr,
    Global,
    Gtxn,
    If,
    Seq,
    Subroutine,
    TealType,
    TxnObject,
    TxnType,
)


@Subroutine(TealType.none)
def validate_transfer(
    txn_id: Expr,
    asset_id: Expr,
    receiver: Expr,
    sender: Expr,
) -> Expr:
    transfer = Gtxn[txn_id]
    return Seq(
        If(asset_id)
        .Then(Assert(validate_asset_transfer(transfer, asset_id, receiver, sender)))
        .Else(Assert(validate_algos_transfer(transfer, receiver, sender)))
    )


def validate_asset_transfer(
    txn: TxnObject,
    asset_id: Optional[Expr] = None,
    receiver: Optional[Expr] = None,
    sender: Optional[Expr] = None,
) -> Expr:
    """
    Perform checks that the transaction is a valid asset transfer.
    By default checks:
        - txn type == asset transfer
        - rekey to == zero address
        - asset close to == zero zddress
    Optionally other fields can be checked.

    Args:
        txn: transaction to check
        asset_id (optional): check if the transferred asset id is equal to this
        receiver (optional): check if the receiver matches with this parameter
        sender (optional): check if the sender matches with this parameter

    Returns:
        `Expr`: expression evaluating to 0 or 1
    """
    checks = [
        txn.type_enum() == TxnType.AssetTransfer,
        txn.rekey_to() == Global.zero_address(),
        txn.asset_close_to() == Global.zero_address(),
    ]
    if asset_id is not None:
        checks.append(txn.xfer_asset() == asset_id)
    if receiver is not None:
        checks.append(txn.asset_receiver() == receiver)
    if sender is not None:
        checks.append(txn.sender() == sender)
    return And(*checks)


def validate_algos_transfer(
    txn: TxnObject, receiver: Optional[Expr] = None, sender: Optional[Expr] = None
) -> Expr:
    """
    Perform checks that the transaction is a valid algos transfer.
    By default checks:
        - txn type == payment
        - rekey to == zero address
        - close remainder to == zero zddress
    Optionally other fields can be checked.

    Args:
        txn: transaction to check
        receiver (optional): check if the receiver matches with this parameter
        sender (optional): check if the sender matches with this parameter

    Returns:
        `Expr`: expression evaluating to 0 or 1
    """
    checks = [
        txn.type_enum() == TxnType.Payment,
        txn.rekey_to() == Global.zero_address(),
        txn.close_remainder_to() == Global.zero_address(),
    ]
    if receiver is not None:
        checks.append(txn.receiver() == receiver)
    if sender is not None:
        checks.append(txn.sender() == sender)
    return And(*checks)
