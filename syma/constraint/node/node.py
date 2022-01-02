from abc import ABC, abstractmethod
from enum import Enum, auto, unique
from typing import TYPE_CHECKING, List, TypeVar, Union

if TYPE_CHECKING:
    from syma.constraint.node.visitor import NodeVisitor

T = TypeVar("T")


@unique
class NodeType(Enum):
    NumConst = auto()
    NumVar = auto()
    BoolConst = auto()
    BoolVar = auto()
    Comparison = auto()
    And = auto()
    Or = auto()
    Not = auto()


class Node(ABC):
    def __init__(self):
        self.children: List["Node"] = list()

    def add_child(self, child: "Node"):
        self.children.append(child)

    @property
    @abstractmethod
    def node_type(self) -> NodeType:
        ...

    def __lt__(self, other: Union["Node", int, float]) -> "LT":
        if isinstance(other, int):
            other = IntConst(other)
        elif isinstance(other, float):
            other = RealConst(other)
        return LT(self, other)

    def __le__(self, other: Union["Node", int, float]) -> "LEQ":
        if isinstance(other, int):
            other = IntConst(other)
        elif isinstance(other, float):
            other = RealConst(other)
        return LEQ(self, other)

    def __gt__(self, other: Union["Node", int, float]) -> "GT":
        if isinstance(other, int):
            other = IntConst(other)
        elif isinstance(other, float):
            other = RealConst(other)
        return GT(self, other)

    def __ge__(self, other: Union["Node", int, float]) -> "GEQ":
        if isinstance(other, int):
            other = IntConst(other)
        elif isinstance(other, float):
            other = RealConst(other)
        return GEQ(self, other)

    def __eq__(self, other: Union["Node", bool, int, float]) -> "EQ":
        if isinstance(other, bool):
            other = BoolConst(other)
        elif isinstance(other, int):
            other = IntConst(other)
        elif isinstance(other, float):
            other = RealConst(other)
        return EQ(self, other)

    def __ne__(self, other: Union["Node", bool, int, float]) -> "NEQ":
        if isinstance(other, bool):
            other = BoolConst(other)
        elif isinstance(other, int):
            other = IntConst(other)
        elif isinstance(other, float):
            other = RealConst(other)
        return NEQ(self, other)

    def __invert__(self) -> "Not":
        return Not(self)

    def __or__(self, other: Union["Node", bool]) -> "Node":
        if isinstance(other, bool):
            other = BoolConst(other)
        if self.is_true() or other.is_true():
            return BoolConst(True)
        if self.is_false():
            return other
        if other.is_false():
            return self
        return Or(self, other)

    def __ror__(self, other: Union["Node", bool]) -> "Node":
        return self.__or__(other)

    def __and__(self, other: Union["Node", bool]) -> "Node":
        if isinstance(other, bool):
            other = BoolConst(other)
        if self.is_false() or other.is_false():
            return BoolConst(False)
        if self.is_true():
            return other
        if other.is_true():
            return self
        return And(self, other)

    def __rand__(self, other: Union["Node", bool]) -> "Node":
        return self.__and__(other)

    @abstractmethod
    def doVisit(self, visitor: "NodeVisitor[T]", *args, **kwargs) -> T:
        ...

    def is_nnf(self) -> bool:
        return False

    def is_true(self) -> bool:
        if self.node_type == NodeType.BoolConst:
            assert isinstance(self, BoolConst)
            return self.value
        return False

    def is_false(self) -> bool:
        if self.node_type == NodeType.BoolConst:
            assert isinstance(self, BoolConst)
            return not self.value
        return False


class BoolConst(Node):
    def __init__(self, value: bool):
        super().__init__()
        self._value = value

    @property
    def value(self) -> bool:
        return self._value

    @property
    def node_type(self) -> NodeType:
        return NodeType.BoolConst

    def __invert__(self) -> Node:
        return BoolConst(not self.value)

    def doVisit(self, visitor: "NodeVisitor[T]", *args, **kwargs) -> T:
        return visitor.visitBoolConst(self, *args, **kwargs)

    def is_nnf(self) -> bool:
        return True

    def __str__(self) -> str:
        return str(self.value)

    def __repr__(self) -> str:
        return f"BoolConst({self.value})"


class IntConst(Node):
    def __init__(self, value: int):
        super().__init__()
        self._value = value

    @property
    def value(self) -> int:
        return self._value

    @property
    def node_type(self) -> NodeType:
        return NodeType.NumConst

    def __invert__(self):
        raise TypeError("Logical negation cannot be applied to IntConst")

    def __str__(self) -> str:
        return str(self.value)

    def __repr__(self) -> str:
        return f"IntConst({self.value})"

    def doVisit(self, visitor: "NodeVisitor[T]", *args, **kwargs) -> T:
        return visitor.visitIntConst(self, *args, **kwargs)


class RealConst(Node):
    def __init__(self, value: float):
        super().__init__()
        self._value = value

    @property
    def value(self) -> float:
        return self._value

    @property
    def node_type(self) -> NodeType:
        return NodeType.NumConst

    def __invert__(self):
        raise TypeError("Logical negation cannot be applied to RealConst")

    def __str__(self) -> str:
        return str(self.value)

    def __repr__(self) -> str:
        return f"RealConst({self.value})"

    def doVisit(self, visitor: "NodeVisitor[T]", *args, **kwargs) -> T:
        return visitor.visitRealConst(self, *args, **kwargs)


def Constant(value: Union[bool, int, float]) -> Node:
    if isinstance(value, bool):
        return BoolConst(value)
    if isinstance(value, int):
        return IntConst(value)
    if isinstance(value, float):
        return RealConst(value)
    raise TypeError(f"Unsupported constant type: {type(value)}")


class BoolVar(Node):
    def __init__(self, name: str):
        super().__init__()
        self._name = name

    @property
    def name(self) -> str:
        return self._name

    @property
    def node_type(self) -> NodeType:
        return NodeType.BoolVar

    def is_nnf(self) -> bool:
        return True

    def __str__(self) -> str:
        return str(self.name)

    def __repr__(self) -> str:
        return f"BoolVar({self.name})"

    def doVisit(self, visitor: "NodeVisitor[T]", *args, **kwargs) -> T:
        return visitor.visitBoolVar(self, *args, **kwargs)


class IntVar(Node):
    def __init__(self, name: str):
        super().__init__()
        self._name = name

    @property
    def name(self) -> str:
        return self._name

    @property
    def node_type(self) -> NodeType:
        return NodeType.NumVar

    def __invert__(self):
        raise TypeError("Logical negation cannot be applied to IntVar")

    def __str__(self) -> str:
        return str(self.name)

    def __repr__(self) -> str:
        return f"IntVar({self.name})"

    def doVisit(self, visitor: "NodeVisitor[T]", *args, **kwargs) -> T:
        return visitor.visitIntVar(self, *args, **kwargs)


class RealVar(Node):
    def __init__(self, name: str):
        super().__init__()
        self._name = name

    @property
    def name(self) -> str:
        return self._name

    @property
    def node_type(self) -> NodeType:
        return NodeType.NumVar

    def __invert__(self):
        raise TypeError("Logical negation cannot be applied to RealVar")

    def __str__(self) -> str:
        return str(self.name)

    def __repr__(self) -> str:
        return f"RealVar({self.name})"

    def doVisit(self, visitor: "NodeVisitor[T]", *args, **kwargs) -> T:
        return visitor.visitRealVar(self, *args, **kwargs)


class LEQ(Node):
    def __init__(self, op1: Node, op2: Node):
        Node.__init__(self)
        self.children.append(op1)
        self.children.append(op2)

    @property
    def node_type(self) -> NodeType:
        return NodeType.Comparison

    def __invert__(self) -> Node:
        return GT(self.children[0], self.children[1])

    def __str__(self):
        return f"({str(self.children[0])} <= {str(self.children[1])})"

    def __repr__(self):
        return f"LEQ({str(self.children[0])}, {str(self.children[1])})"

    def doVisit(self, visitor: "NodeVisitor[T]", *args, **kwargs) -> T:
        return visitor.visitLEQ(self, *args, **kwargs)

    def is_nnf(self) -> bool:
        return True


class LT(Node):
    def __init__(self, op1: Node, op2: Node):
        Node.__init__(self)
        self.children.append(op1)
        self.children.append(op2)

    @property
    def node_type(self) -> NodeType:
        return NodeType.Comparison

    def __invert__(self) -> Node:
        return GEQ(self.children[0], self.children[1])

    def __str__(self):
        return f"({str(self.children[0])} < {str(self.children[1])})"

    def __repr__(self):
        return f"LT({str(self.children[0])}, {str(self.children[1])})"

    def doVisit(self, visitor: "NodeVisitor[T]", *args, **kwargs) -> T:
        return visitor.visitLT(self, *args, **kwargs)

    def is_nnf(self) -> bool:
        return True


class GEQ(Node):
    def __init__(self, op1: Node, op2: Node):
        Node.__init__(self)
        self.children.append(op1)
        self.children.append(op2)

    @property
    def node_type(self) -> NodeType:
        return NodeType.Comparison

    def __invert__(self) -> Node:
        return LT(self.children[0], self.children[1])

    def __str__(self):
        return f"({str(self.children[0])} >= {str(self.children[1])})"

    def __repr__(self):
        return f"GEQ({str(self.children[0])}, {str(self.children[1])})"

    def doVisit(self, visitor: "NodeVisitor[T]", *args, **kwargs) -> T:
        return visitor.visitGEQ(self, *args, **kwargs)

    def is_nnf(self) -> bool:
        return True


class GT(Node):
    def __init__(self, op1: Node, op2: Node):
        Node.__init__(self)
        self.children.append(op1)
        self.children.append(op2)

    @property
    def node_type(self) -> NodeType:
        return NodeType.Comparison

    def __invert__(self) -> Node:
        return LEQ(self.children[0], self.children[1])

    def __str__(self):
        return f"({str(self.children[0])} > {str(self.children[1])})"

    def __repr__(self):
        return f"GT({str(self.children[0])}, {str(self.children[1])})"

    def doVisit(self, visitor: "NodeVisitor[T]", *args, **kwargs) -> T:
        return visitor.visitGT(self, *args, **kwargs)

    def is_nnf(self) -> bool:
        return True


class EQ(Node):
    def __init__(self, op1: Node, op2: Node):
        Node.__init__(self)
        self.children.append(op1)
        self.children.append(op2)

    @property
    def node_type(self) -> NodeType:
        return NodeType.Comparison

    def __invert__(self) -> Node:
        return NEQ(self.children[0], self.children[1])

    def __str__(self):
        return f"({str(self.children[0])} == {str(self.children[1])})"

    def __repr__(self):
        return f"EQ({str(self.children[0])}, {str(self.children[1])})"

    def doVisit(self, visitor: "NodeVisitor[T]", *args, **kwargs) -> T:
        return visitor.visitEQ(self, *args, **kwargs)

    def is_nnf(self) -> bool:
        return True


class NEQ(Node):
    def __init__(self, op1: Node, op2: Node):
        Node.__init__(self)
        self.children.append(op1)
        self.children.append(op2)

    @property
    def node_type(self) -> NodeType:
        return NodeType.Comparison

    def __invert__(self) -> Node:
        return EQ(self.children[0], self.children[1])

    def __str__(self):
        return f"({str(self.children[0])} != {str(self.children[1])})"

    def __repr__(self):
        return f"NEQ({str(self.children[0])}, {str(self.children[1])})"

    def doVisit(self, visitor: "NodeVisitor[T]", *args, **kwargs) -> T:
        return visitor.visitNEQ(self, *args, **kwargs)

    def is_nnf(self) -> bool:
        return True


class Not(Node):
    def __init__(self, op: Node):
        Node.__init__(self)
        self.children.append(op)

    @property
    def node_type(self) -> NodeType:
        return NodeType.Not

    def __str__(self):
        return f"not {str(self.children[0])}"

    def __repr__(self):
        return f"Not({str(self.children[0])})"

    def doVisit(self, visitor: "NodeVisitor[T]", *args, **kwargs) -> T:
        return visitor.visitNot(self, *args, **kwargs)

    def is_nnf(self) -> bool:
        return False


class And(Node):
    def __init__(self, *ops: Node):
        Node.__init__(self)
        if len(ops) < 2:
            raise ValueError("At least 2 operands required by AND")
        self.children = []
        for op in ops:
            if op.node_type == NodeType.And:
                self.children.extend(op.children)
            else:
                self.children.append(op)

    @property
    def node_type(self) -> NodeType:
        return NodeType.And

    def __str__(self):
        s = " & ".join([str(child) for child in self.children])
        return f"({s})"

    def __repr__(self):
        children = ", ".join([f"{repr(child)}" for child in self.children])
        return f"And({children})"

    def doVisit(self, visitor: "NodeVisitor[T]", *args, **kwargs) -> T:
        return visitor.visitAnd(self, *args, **kwargs)

    def is_nnf(self) -> bool:
        for child in self.children:
            if not child.is_nnf():
                return False
        return True


class Or(Node):
    def __init__(self, *ops: Node):
        Node.__init__(self)
        if len(ops) < 2:
            raise ValueError("At least 2 operands required by OR")
        self.children = []
        for op in ops:
            if op.node_type == NodeType.Or:
                self.children.extend(op.children)
            else:
                self.children.append(op)

    @property
    def node_type(self) -> NodeType:
        return NodeType.Or

    def __str__(self):
        s = " | ".join([str(child) for child in self.children])
        return f"({s})"

    def __repr__(self):
        children = ", ".join([f"{repr(child)}" for child in self.children])
        return f"Or({children})"

    def doVisit(self, visitor: "NodeVisitor[T]", *args, **kwargs) -> T:
        return visitor.visitOr(self, *args, **kwargs)

    def is_nnf(self) -> bool:
        for child in self.children:
            if not child.is_nnf():
                return False
        return True
