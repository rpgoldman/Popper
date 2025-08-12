from typing import FrozenSet, NamedTuple, Tuple
from clingo import Symbol


class Literal(NamedTuple):
    predicate: str
    arguments: Tuple[Symbol, ...]


Rule = Tuple[Literal, FrozenSet[Literal]]
RuleBase = FrozenSet[Rule]
