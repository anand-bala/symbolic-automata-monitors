from typing import TYPE_CHECKING, Mapping, Optional, Union

import z3

from syma.constraint.helpers.evaluate import evaluate_formula
from syma.constraint.helpers.minimization import minimize_formula
from syma.constraint.helpers.smt import (
    check_trivially_false,
    check_trivially_true,
    to_smt,
)
from syma.constraint.helpers.transform import to_dnf, to_nnf
from syma.constraint.node.node import (
    BoolConst,
    BoolVar,
    IntVar,
    Node,
    NodeType,
    RealVar,
)

if TYPE_CHECKING:
    from syma.alphabet import Alphabet


Value = Union[bool, int, float]
VarNode = Union[BoolVar, IntVar, RealVar]


class Constraint(object):
    def __init__(self, alphabet: "Alphabet", formula: Union[Node, bool]):
        self._alphabet = alphabet
        if isinstance(formula, bool):
            formula = BoolConst(formula)

        self._formula = formula
        self._smt_formula: Optional[z3.ExprRef] = None

        self._is_trivially_false: Optional[bool] = None
        self._is_trivially_true: Optional[bool] = None

    @property
    def formula(self) -> Node:
        return self._formula

    @property
    def alphabet(self):
        return self._alphabet

    @property
    def expr(self) -> z3.ExprRef:
        if self._smt_formula is None:
            self._smt_formula = to_smt(self._formula)
        return self._smt_formula

    def is_sat(self) -> bool:
        """Check if the formula is satisfiable"""
        return not self.is_trivially_false()

    def is_trivially_false(self) -> bool:
        """Check if the formula is trivially false"""
        if self.formula.node_type == NodeType.BoolConst:
            return self.formula.value is False  # type: ignore
        if self._is_trivially_false is not None:
            return self._is_trivially_false
        self._is_trivially_false = check_trivially_false(self.expr)
        if self._is_trivially_false:
            self._formula = BoolConst(False)

        return self._is_trivially_false

    def is_trivially_true(self) -> bool:
        """Check if the formula is trivially true"""
        if self.formula.node_type == NodeType.BoolConst:
            return self.formula.value  # type: ignore
        if self._is_trivially_true is not None:
            return self._is_trivially_true
        self._is_trivially_true = check_trivially_true(
            self.alphabet.get_z3_vars(), self.expr
        )
        if self._is_trivially_true:
            self._formula = BoolConst(True)
        return self._is_trivially_true

    def check_sat(self, values: Mapping[str, Value]) -> bool:
        return evaluate_formula(self.formula, values)

    def to_nnf(self) -> "Constraint":
        return Constraint(self.alphabet, to_nnf(self.formula))

    def to_dnf(self) -> "Constraint":
        return Constraint(self.alphabet, to_dnf(self.formula))

    def minimize(self) -> "Constraint":
        dnf = self.to_dnf()
        minim = minimize_formula(self.alphabet, dnf.formula)
        return Constraint(self.alphabet, minim)

    def __repr__(self):
        return repr(self._formula)

    def __str__(self):
        return str(self._formula)
