from dataclasses import dataclass
from typing import Iterable, Iterator, List, Optional, Tuple, Union

import numpy as np
import z3

from syma.constraint.node import BoolVar, IntVar, NodeType, RealVar

Num = Union[int, float]
VarNode = Union[BoolVar, IntVar, RealVar]


@dataclass(order=True, eq=True, frozen=True)
class Interval:
    low: float
    high: float

    def __init__(self, low: float, high: float) -> None:
        if low > high:
            # Empty set, so make it standard (1, 0)
            object.__setattr__(self, "low", 1)
            object.__setattr__(self, "high", 0)
        else:
            object.__setattr__(self, "low", low)
            object.__setattr__(self, "high", high)

    @staticmethod
    def create_empty() -> "Interval":
        return Interval(low=1, high=0)

    def as_tuple(self) -> Tuple[float, float]:
        return self.low, self.high

    def __iter__(self) -> Iterator[float]:
        return iter(self.as_tuple())

    def __contains__(self, val: float) -> bool:
        if self.is_empty():
            return False
        return self.low <= val <= self.high

    def is_empty(self) -> bool:
        return self.low > self.high

    def is_disjoint(self, other: "Interval") -> bool:
        return not self.overlaps(other)

    def is_subset(self, other: "Interval") -> bool:
        """Check if this interval is fully contained within the other"""

        # Essentially, check if we intersect with other and if the intersection is
        # equal to us.
        intersection = self.intersect(other)
        if self == intersection:
            return True
        return False

    def is_bounded(self) -> bool:
        if np.isinf(abs(self.low)) or np.isinf(abs(self.high)):
            return False
        else:
            return True

    def is_unbounded(self) -> bool:
        return not self.is_bounded()

    def overlaps(self, other: "Interval") -> bool:
        if self.is_empty() or other.is_empty():
            return False

        low1, high1 = self.low, self.high
        low2, high2 = other.low, other.high

        if low2 <= low1 <= high2:
            # Int1 starts within Int2
            return True
        elif low2 <= high1 <= high2:
            # Int1 ends within Int2
            return True
        return False

    def intersect(self, other: "Interval") -> "Interval":
        if self.is_empty() or other.is_empty() or self.is_disjoint(other):
            return self.create_empty()

        low1, high1 = self.low, self.high
        low2, high2 = other.low, other.high

        low = max(low1, low2)
        high = min(high1, high2)

        return Interval(low=low, high=high)

    def union(self, other: "Interval") -> List["Interval"]:
        if self.is_empty() and other.is_empty():
            return [self.create_empty()]
        if self.is_empty():
            return [other]
        if other.is_empty():
            return [self]
        if self.is_disjoint(other):
            return [self, other]

        # Overlaps
        low1, high1 = self.low, self.high
        low2, high2 = other.low, other.high

        low = min(low1, low2)
        high = max(high1, high2)

        return [Interval(low=low, high=high)]


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

    def __init__(self) -> None:
        self.vars: dict[str, VarNode] = dict()  # Map of variable names to variable node
        self.domains: dict[str, Interval] = dict()  # Domain Map

    def __eq__(self, other: "Alphabet") -> bool:
        if set(self.vars.keys()) != set(other.vars.keys()):
            return False
        if set(self.domains) != set(other.domains):
            return False

        for key in self.vars.keys():
            var1 = self.get_var(key)
            var2 = other.get_var(key)
            if var1.node_type != var2.node_type:
                return False
            if var1.name != var2.name:
                return False

            domain1 = self.get_domain(key)
            domain2 = other.get_domain(key)
            if domain1 != domain2:
                return False

        return True

    def declare_bool(self, name: str) -> BoolVar:
        var = BoolVar(name)
        self.add_var(var, None)
        return var

    def declare_int(self, name: str, domain: Optional[Interval] = None) -> IntVar:
        var = IntVar(name)
        self.add_var(var, domain)
        return var

    def declare_real(self, name: str, domain: Optional[Interval] = None) -> RealVar:
        var = RealVar(name)
        self.add_var(var, domain)
        return var

    def add_var(self, var: VarNode, domain: Optional[Interval] = None):
        assert var.node_type in [NodeType.BoolVar, NodeType.NumVar]
        if var.name in self.vars:
            raise ValueError(f"Redeclaration of variable {var.name}")
        if domain is None:
            if var.node_type == NodeType.BoolVar:
                assert isinstance(var, BoolVar)
                domain = Interval(0, 1)
            else:  # var.node_type == NodeType.NumVar:
                assert isinstance(var, (IntVar, RealVar))
                domain = Interval(-np.inf, np.inf)

        assert domain is not None

        self.vars[var.name] = var
        self.domains[var.name] = domain

    def get_var(self, var_name: str) -> VarNode:
        return self.vars[var_name]

    def get_domain(self, var_name: str) -> Interval:
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
        if domain.is_empty():
            return None
        else:
            low, high = domain.as_tuple()
            return z3.And(var >= low, var <= high)  #  type: ignore
