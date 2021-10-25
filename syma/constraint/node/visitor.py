from abc import ABC, abstractmethod

from syma.constraint.node.node import (EQ, GEQ, GT, LEQ, LT, NEQ, And,
                                       BoolConst, BoolVar, IntConst, IntVar,
                                       Node, Not, Or, RealConst, RealVar)

NOT_IMPLEMENTED = "You should implement this."

from typing import Generic, TypeVar

T = TypeVar("T")


class NodeVisitor(Generic[T], ABC):
    def visit(self, node: Node, *args) -> T:
        if isinstance(node, BoolConst):
            return self.visitBoolConst(node, *args)
        if isinstance(node, IntConst):
            return self.visitIntConst(node, *args)
        if isinstance(node, RealConst):
            return self.visitRealConst(node, *args)
        if isinstance(node, BoolVar):
            return self.visitBoolVar(node, *args)
        if isinstance(node, IntVar):
            return self.visitIntVar(node, *args)
        if isinstance(node, RealVar):
            return self.visitRealVar(node, *args)
        if isinstance(node, EQ):
            return self.visitEQ(node, *args)
        if isinstance(node, GEQ):
            return self.visitGEQ(node, *args)
        if isinstance(node, GT):
            return self.visitGT(node, *args)
        if isinstance(node, LEQ):
            return self.visitLEQ(node, *args)
        if isinstance(node, LT):
            return self.visitLT(node, *args)
        if isinstance(node, NEQ):
            return self.visitNEQ(node, *args)
        if isinstance(node, Not):
            return self.visitNot(node, *args)
        if isinstance(node, And):
            return self.visitAnd(node, *args)
        if isinstance(node, Or):
            return self.visitOr(node, *args)
        else:
            raise Exception("Node Visitor: unexpected method called.")

    @abstractmethod
    def visitBoolConst(self, node: BoolConst, *args) -> T:
        raise NotImplementedError(NOT_IMPLEMENTED)

    @abstractmethod
    def visitIntConst(self, node: IntConst, *args) -> T:
        raise NotImplementedError(NOT_IMPLEMENTED)

    @abstractmethod
    def visitRealConst(self, node: RealConst, *args) -> T:
        raise NotImplementedError(NOT_IMPLEMENTED)

    @abstractmethod
    def visitBoolVar(self, node: BoolVar, *args) -> T:
        raise NotImplementedError(NOT_IMPLEMENTED)

    @abstractmethod
    def visitIntVar(self, node: IntVar, *args) -> T:
        raise NotImplementedError(NOT_IMPLEMENTED)

    @abstractmethod
    def visitRealVar(self, node: RealVar, *args) -> T:
        raise NotImplementedError(NOT_IMPLEMENTED)

    @abstractmethod
    def visitGEQ(self, node: GEQ, *args) -> T:
        raise NotImplementedError(NOT_IMPLEMENTED)

    @abstractmethod
    def visitGT(self, node: GT, *args) -> T:
        raise NotImplementedError(NOT_IMPLEMENTED)

    @abstractmethod
    def visitLEQ(self, node: LEQ, *args) -> T:
        raise NotImplementedError(NOT_IMPLEMENTED)

    @abstractmethod
    def visitLT(self, node: LT, *args) -> T:
        raise NotImplementedError(NOT_IMPLEMENTED)

    @abstractmethod
    def visitEQ(self, node: EQ, *args) -> T:
        raise NotImplementedError(NOT_IMPLEMENTED)

    @abstractmethod
    def visitNEQ(self, node: NEQ, *args) -> T:
        raise NotImplementedError(NOT_IMPLEMENTED)

    @abstractmethod
    def visitNot(self, node: Not, *args) -> T:
        raise NotImplementedError(NOT_IMPLEMENTED)

    @abstractmethod
    def visitAnd(self, node: And, *args) -> T:
        raise NotImplementedError(NOT_IMPLEMENTED)

    @abstractmethod
    def visitOr(self, node: Or, *args) -> T:
        raise NotImplementedError(NOT_IMPLEMENTED)
