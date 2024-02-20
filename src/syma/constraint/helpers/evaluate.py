from typing import Mapping, Union

from syma.constraint.node import (
    EQ,
    GEQ,
    GT,
    LEQ,
    LT,
    NEQ,
    And,
    BoolConst,
    BoolVar,
    IntConst,
    IntVar,
    Node,
    NodeVisitor,
    Not,
    Or,
    RealConst,
    RealVar,
)


class Evaluate(NodeVisitor[Union[bool, int, float]]):
    """Evaluate a formula

    Given a formula and a valuation for each variable in the formula, compute it's
    boolean satisfaction value.
    """

    def __init__(self, formula: Node, value: Mapping[str, Union[bool, int, float]]):
        self.formula = formula
        self.value = value

    def evaluate(self) -> bool:
        val = self.visit(self.formula)
        assert isinstance(
            val, bool
        ), "Looks like the formula you're evaluating is ill-formed"
        return val

    def visitBoolConst(self, node: BoolConst) -> bool:
        return node.value

    def visitIntConst(self, node: IntConst) -> int:
        return node.value

    def visitRealConst(self, node: RealConst) -> float:
        return node.value

    def visitBoolVar(self, node: BoolVar) -> bool:
        val = bool(self.value[node.name])
        return val

    def visitIntVar(self, node: IntVar) -> int:
        val = int(self.value[node.name])
        return val

    def visitRealVar(self, node: RealVar) -> float:
        val = float(self.value[node.name])
        return val

    def visitEQ(self, node: EQ) -> bool:
        lhs = self.visit(node.children[0])
        rhs = self.visit(node.children[1])
        return lhs == rhs

    def visitNEQ(self, node: NEQ) -> bool:
        lhs = self.visit(node.children[0])
        rhs = self.visit(node.children[1])
        return lhs != rhs

    def visitGEQ(self, node: GEQ) -> bool:
        lhs = self.visit(node.children[0])
        rhs = self.visit(node.children[1])
        return lhs >= rhs

    def visitGT(self, node: GT) -> bool:
        lhs = self.visit(node.children[0])
        rhs = self.visit(node.children[1])
        return lhs > rhs

    def visitLEQ(self, node: LEQ) -> bool:
        lhs = self.visit(node.children[0])
        rhs = self.visit(node.children[1])
        return lhs <= rhs

    def visitLT(self, node: LT) -> bool:
        lhs = self.visit(node.children[0])
        rhs = self.visit(node.children[1])
        return lhs < rhs

    def visitNot(self, node: Not) -> bool:
        child = self.visit(node.children[0])
        return not child

    def visitOr(self, node: Or) -> bool:
        expr = False
        for child in node.children:
            expr = expr or self.visit(child)
        assert isinstance(expr, bool)
        return expr

    def visitAnd(self, node: And) -> bool:
        expr = True
        for child in node.children:
            expr = expr and self.visit(child)
        assert isinstance(expr, bool)
        return expr


def evaluate_formula(
    formula: Node, valuation: Mapping[str, Union[bool, int, float]]
) -> bool:
    return Evaluate(formula, valuation).evaluate()
