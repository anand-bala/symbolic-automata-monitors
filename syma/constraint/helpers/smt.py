from typing import Iterable

import z3

from syma.constraint.node import (EQ, GEQ, GT, LEQ, LT, NEQ, And, BoolConst,
                                  BoolVar, IntConst, IntVar, Node, NodeVisitor,
                                  Not, Or, RealConst, RealVar)


class Formula2SMT(NodeVisitor[z3.ExprRef]):
    def __init__(self, formula: Node):
        self.formula = formula

    def translate(self) -> z3.ExprRef:
        return self.visit(self.formula)

    def visitBoolConst(self, node: BoolConst) -> z3.ExprRef:
        return z3.BoolVal(node.value)

    def visitIntConst(self, node: IntConst) -> z3.ExprRef:
        return z3.IntVal(node.value)

    def visitRealConst(self, node: RealConst) -> z3.ExprRef:
        return z3.RealVal(node.value)

    def visitBoolVar(self, node: BoolVar) -> z3.ExprRef:
        return z3.Bool(node.name)

    def visitIntVar(self, node: IntVar) -> z3.ExprRef:
        return z3.Int(node.name)

    def visitRealVar(self, node: RealVar) -> z3.ExprRef:
        return z3.Real(node.name)

    def visitEQ(self, node: EQ) -> z3.ExprRef:
        op1 = self.visit(node.children[0])
        op2 = self.visit(node.children[1])
        return op1 == op2  # type: ignore

    def visitNEQ(self, node: NEQ) -> z3.ExprRef:
        op1 = self.visit(node.children[0])
        op2 = self.visit(node.children[1])
        return op1 != op2  # type: ignore

    def visitGEQ(self, node: GEQ) -> z3.ExprRef:
        op1 = self.visit(node.children[0])
        op2 = self.visit(node.children[1])
        return op1 >= op2  # type: ignore

    def visitGT(self, node: GT) -> z3.ExprRef:
        op1 = self.visit(node.children[0])
        op2 = self.visit(node.children[1])
        return op1 > op2  # type: ignore

    def visitLT(self, node: LT) -> z3.ExprRef:
        op1 = self.visit(node.children[0])
        op2 = self.visit(node.children[1])
        return op1 < op2  # type: ignore

    def visitLEQ(self, node: LEQ) -> z3.ExprRef:
        op1 = self.visit(node.children[0])
        op2 = self.visit(node.children[1])
        return op1 <= op2  # type: ignore

    def visitNot(self, node: Not) -> z3.ExprRef:
        op = self.visit(node.children[0])
        return z3.Not(op)  # type: ignore

    def visitAnd(self, node: And) -> z3.ExprRef:
        ops = [self.visit(child) for child in node.children]
        return z3.And(*ops)  # type: ignore

    def visitOr(self, node: Or) -> z3.ExprRef:
        ops = [self.visit(child) for child in node.children]
        return z3.Or(*ops)  # type: ignore


def to_smt(formula: Node) -> z3.ExprRef:
    return Formula2SMT(formula).translate()


def check_trivially_false(formula: z3.ExprRef) -> bool:
    solver = z3.Solver()
    solver.add(formula)
    result = solver.check()

    return result == z3.unsat


def check_trivially_true(vars: Iterable[z3.ExprRef], expr: z3.ExprRef) -> bool:
    solver = z3.Solver()
    solver.add(z3.ForAll(list(vars), expr))
    result = solver.check()

    return result == z3.sat
