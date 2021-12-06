from typing import Iterable, Optional, Tuple, Union

import z3

from syma.constraint.node import BoolVar, IntVar, NodeType, RealVar

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

    def declare_bool(self, name: str) -> BoolVar:
        var = BoolVar(name)
        self.add_var(var, None)
        return var

    def declare_int(self, name: str, domain: Optional[Tuple] = None) -> IntVar:
        var = IntVar(name)
        self.add_var(var, domain)
        return var

    def declare_real(self, name: str, domain: Optional[Tuple] = None) -> RealVar:
        var = RealVar(name)
        self.add_var(var, domain)
        return var

    def add_var(self, var: VarNode, domain: Optional[Tuple] = None):
        assert var.node_type in [NodeType.BoolVar, NodeType.NumVar]
        if var.name in self.vars:
            raise ValueError(f"Redeclaration of variable {var.name}")
        self.vars[var.name] = var
        self.domains[var.name] = domain

    def get_var(self, var_name: str) -> VarNode:
        return self.vars[var_name]

    def get_domain(self, var_name: str) -> Optional[Tuple]:
        return self.domains[var_name]

    def get_z3_vars(self) -> Iterable[z3.ExprRef]:
        for var in self.vars.keys():
            yield self.get_z3_var(var)

    def get_z3_var(self, var_name: str) -> z3.ExprRef:
        var = self.get_var(var_name)
        if isinstance(var, BoolVar):
            return z3.Bool(var.name)
        if isinstance(var, IntVar):
            return z3.Int(var.name)
        if isinstance(var, RealVar):
            return z3.Real(var.name)

        return NotImplemented

    def get_z3_domain(self, var_name: str) -> Optional[z3.BoolRef]:
        domain = self.get_domain(var_name)
        var = self.get_z3_var(var_name)
        if domain is None:
            return None
        low, high = domain
        return z3.And(var >= low, var <= high)  #  type: ignore
