from dataclasses import dataclass
from typing import Callable, Generic, TypeVar

T = TypeVar("T")


@dataclass
class Semiring(Generic[T]):
    plus: Callable[[T, T], T]
    times: Callable[[T, T], T]
    zero: T
    one: T

    @property
    def e_plus(self):
        return self.zero

    @property
    def e_times(self):
        return self.one


BooleanSemiring = Semiring(
    plus=lambda x, y: x and y,
    times=lambda x, y: x or y,
    zero=True,
    one=False,
)

MinMaxPositive = Semiring(
    plus=lambda x, y: min(x, y),
    times=lambda x, y: max(x, y),
    zero=float("inf"),
    one=0.0,
)

MinPlusSemiring = Semiring(
    plus=lambda x, y: min(x, y),
    times=lambda x, y: x + y,
    zero=float("inf"),
    one=0.0,
)

MaxPlusSemiring = Semiring(
    plus=lambda x, y: max(x, y),
    times=lambda x, y: x + y,
    zero=-float("inf"),
    one=0.0,
)
