from typing import (Generic, Iterable, NamedTuple, Optional, Tuple, TypeVar,
                    Union)

import z3

from syma.constraint.node import BoolVar, IntVar, Node, RealVar

VarNode = Union[BoolVar, IntVar, RealVar]


class Alphabet(object):
    """An effective Boolean alphabet.

    An effective Boolean algebra (alphabet) $A$ is the tuple A = (X, D, Pred, or, and, not)
    * X - is a set of variables
    * D - is the domain of the variables in X
    * Pred - is a set of atomic predicates over variables in X
    * or - is the disjunction operation
    * and - is the conjunction operation
    * not - is the negation operation

    In this class, we maintain a list of variables and domain mappings.
    """

    def __init__(self):
        self.vars: dict[str, VarNode] = dict()  # Map of variable names to variable node
        self.domains: dict[str, Optional[Tuple]] = dict()  # Domain Map

    def declare_bool(self, name: str, domain: Optional[Tuple] = None) -> BoolVar:
        var = BoolVar(name)
        self.add_var(var, domain)
        return var

    def declare_int(self, name: str, domain: Optional[Tuple] = None) -> IntVar:
        var = IntVar(name)
        self.add_var(var, domain)
        return var

    def declare_real(self, name: str, domain: Optional[Tuple] = None) -> RealVar:
        var = RealVar(name)
        self.add_var(var, domain)
        return var

    def add_var(self, var: VarNode, domain: Optional[Tuple]):
        assert isinstance(var, (BoolVar, IntVar, RealVar))
        if var.name in self.vars:
            raise ValueError(f"Redeclaration of variable {var.name}")
        self.vars[var.name] = var
        self.domains[var.name] = domain

    def get_var(self, var_name: str) -> VarNode:
        return self.vars[var_name]

    def get_domain(self, var_name: str) -> Optional[Tuple]:
        return self.domains[var_name]

    def get_z3_vars(self) -> Iterable[z3.ExprRef]:
        for var in self.vars.values():
            if isinstance(var, BoolVar):
                yield z3.Bool(var.name)
            if isinstance(var, IntVar):
                yield z3.Int(var.name)
            if isinstance(var, RealVar):
                yield z3.Real(var.name)
