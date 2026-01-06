import base64
from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import Type

from algosdk.source_map import SourceMap
from algosdk.transaction import StateSchema
from algosdk.v2client.algod import AlgodClient
from beaker import AppPrecompile, Precompile
from pyteal import MAX_PROGRAM_VERSION, Expr, Mode, compileTeal


@dataclass
class CompiledContract:
    """Compiled contract with all relevant information for deployment and debugging"""

    version: int
    approval_teal: str
    clear_state_teal: str
    approval_bytes: bytes
    clear_state_bytes: bytes
    approval_map: SourceMap
    clear_state_map: SourceMap
    global_schema: StateSchema
    local_schema: StateSchema

    @property
    def extra_pages(self) -> int:
        """Get the required extra pages for the contract"""
        return (len(self.approval_bytes) + len(self.clear_state_bytes)) // 2048


class Contract(ABC):
    """
    Interface for an Algorand contract.
    """

    # Subclass to compiled code mapping
    compiled_contracts: dict[str, CompiledContract] = {}

    @abstractmethod
    def get_program(self) -> Expr:
        """Get the AST of the contract"""

    @abstractmethod
    def get_clear_program(self) -> Expr:
        """Get the clear state program's AST"""

    def get_global_schema(self) -> StateSchema:
        """Get the global state schema"""
        return StateSchema(0, 0)

    def get_local_schema(self) -> StateSchema:
        """Get the local state schema"""
        return StateSchema(0, 0)

    @classmethod
    def compile(cls, client: AlgodClient, cached: bool = True) -> CompiledContract:
        """Compile the contract"""
        version = MAX_PROGRAM_VERSION

        if cls.__name__ in cls.compiled_contracts and cached:
            return cls.compiled_contracts[cls.__name__]

        contract = cls()
        approval = compileTeal(contract.get_program(), Mode.Application, version=version)
        clear = compileTeal(contract.get_clear_program(), Mode.Application, version=version)

        result_approval = client.compile(approval, True)
        result_clear = client.compile(clear, True)

        cc = CompiledContract(
            version,
            approval,
            clear,
            base64.b64decode(result_approval["result"]),
            base64.b64decode(result_clear["result"]),
            SourceMap(result_approval["sourcemap"]),
            SourceMap(result_clear["sourcemap"]),
            contract.get_global_schema(),
            contract.get_local_schema(),
        )

        if cached:
            cls.compiled_contracts[cls.__name__] = cc

        return cc


class ContractTemplate(ABC):
    """
    An Algorand contract that compiles to a TEAL template and has to be post-processed
    before on-chain deployment.
    Generated code must be fully static, however state schema size can vary.
    """

    @classmethod
    @abstractmethod
    def get_program(cls) -> Expr:
        """Get the AST of the contract"""

    @classmethod
    @abstractmethod
    def get_clear_program(cls) -> Expr:
        """Get the clear state program's AST"""

    @abstractmethod
    def get_global_schema(self) -> StateSchema:
        """Get the global state schema"""

    @abstractmethod
    def get_local_schema(self) -> StateSchema:
        """Get the local state schema"""

    def get_extra_pages(self) -> int:
        """Get the number of extra pages required for the contract"""
        return 0

    @abstractmethod
    def get_template_substitutions(self) -> dict[str, str]:
        """
        Return the values that must be substituted during contract deployment.
        Because the .get_program() method returns the contract template,
        the TMPL_* values must be replaced with the actual values.
        """


class ContractPrecompile(AppPrecompile):
    """Specialized AppPrecompile adapter for Contract subclasses"""

    def __init__(self, contract: Type[Contract]):
        self.contract = contract
        self.approval = Precompile("")
        self.clear = Precompile("")
        self.compiled: CompiledContract | None = None

    def compile(self, client: AlgodClient):
        if self.approval._binary is None or self.clear._binary is None:
            self.compiled = self.contract.compile(client)
            self.approval = Precompile(self.compiled.approval_teal)
            self.clear = Precompile(self.compiled.clear_state_teal)

            self.approval.assemble(client)
            self.clear.assemble(client)

    @property
    def extra_pages(self) -> int:
        """Get the required extra pages for the contract should it be deployed

        We can't use get_create_config() from superclass, because it requires the app field
        to be set.
        """
        assert self.approval._binary is not None
        assert self.clear._binary is not None
        return (len(self.approval._binary) + len(self.clear._binary)) // 2048
