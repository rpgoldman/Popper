from typing import FrozenSet, NamedTuple, Optional, Tuple, Literal as TypingLiteral, Union
from clingo import Symbol


class Literal(NamedTuple):
    predicate: str
    arguments: Tuple[Symbol, ...]

class NumericLiteral(NamedTuple):
    predicate: str
    arguments: Tuple[int, ...]

    # idempotent translator...
    @staticmethod
    def from_tuple(tup: Union[Tuple[str,Tuple[int, ...]],'NumericLiteral']) -> 'NumericLiteral':
        if isinstance(tup, NumericLiteral):
            return tup
        assert len(tup) == 2
        predicate, arguments = tup
        if not isinstance(predicate, str):
            raise TypeError("Literal predicate must be a string. Got {}, of type {}".format(predicate, type(predicate)))
        if not isinstance(arguments, tuple) and all(map(lambda x: isinstance(x, int), arguments)):
            raise TypeError("Literal arguments must be a tuple of integers. Got {}.".format(arguments))
        return NumericLiteral(predicate, arguments)


Rule = Tuple[Literal, FrozenSet[Literal]]
# Note the NumericRule could be a constraint (i.e., have None as its head).
NumericRule = Tuple[Optional[NumericLiteral], FrozenSet[NumericLiteral]]
RuleBase = FrozenSet[Rule]
NumericRuleBase = FrozenSet[NumericRule]

Bit = TypingLiteral[0, 1]
