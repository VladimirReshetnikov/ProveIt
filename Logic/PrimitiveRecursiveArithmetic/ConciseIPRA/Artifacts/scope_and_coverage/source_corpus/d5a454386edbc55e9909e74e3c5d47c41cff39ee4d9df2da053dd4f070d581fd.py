"""Finite representation of the report's countable countermodel.

This illustrates specific witnesses and automorphisms. The universal
induction and non-bi-interpretability results are proved in the report;
these finite examples are not substitutes for those proofs. This module
is not imported by any proof checker.
"""
from dataclasses import dataclass
import json


@dataclass(frozen=True)
class Sequence:
    tail: int
    exceptions: tuple = ()

    @classmethod
    def make(cls, tail, values=None):
        values = values or {}
        if not isinstance(tail, int) or tail < 0:
            raise ValueError('A tail must be a natural number')
        if any(not isinstance(i, int) or not isinstance(v, int) or i < 0 or v < 0
               for i, v in values.items()):
            raise ValueError('Coordinates and values must be natural numbers')
        return cls(tail, tuple(sorted((i, v) for i, v in values.items() if v != tail)))

    def at(self, coordinate):
        return dict(self.exceptions).get(coordinate, self.tail)

    def swap(self, first, second):
        support = {i for i, _ in self.exceptions} | {first, second}
        def source(i):
            return second if i == first else first if i == second else i
        return Sequence.make(self.tail, {i: self.at(source(i)) for i in support})

    def description(self):
        return {'eventual_value': self.tail, 'exceptions': dict(self.exceptions)}


def pointwise(function, *arguments):
    """Lift one fixed finitary numerical function to eventual sequences."""
    support = set().union(*({i for i, _ in a.exceptions} for a in arguments))
    tail = function(*(a.tail for a in arguments))
    return Sequence.make(tail, {i: function(*(a.at(i) for a in arguments))
                                for i in support})


def main():
    zero, one = Sequence.make(0), Sequence.make(1)
    spike = Sequence.make(0, {17: 1})
    sign = lambda n: int(n != 0)
    successor = lambda n: n + 1
    predecessor = lambda n: max(n - 1, 0)
    sign_spike = pointwise(sign, spike)
    successor_spike = pointwise(successor, spike)
    parameters = (Sequence.make(5, {2: 7, 9: 0}),
                  Sequence.make(3, {9: 4, 11: 8}))
    transpose = lambda a: a.swap(17, 18)
    moved = transpose(spike)
    assertions = {
        'spike_is_not_zero': spike != zero,
        'spike_is_not_a_successor': spike.tail == 0,
        'Boolean_range_fails': sign_spike not in (zero, one),
        'Boolean_base_holds': pointwise(sign, zero) == zero,
        'Boolean_successor_instance_holds': pointwise(sign, successor_spike) == one,
        'predecessor_computation_holds': pointwise(predecessor, successor_spike) == spike,
        'parameters_are_fixed': all(transpose(a) == a for a in parameters),
        'automorphism_is_nonidentity': moved != spike,
        'automorphism_has_order_two': transpose(moved) == spike,
    }
    for name, function, arguments in (
            ('successor', successor, (spike,)),
            ('addition', lambda a, b: a + b, (spike, parameters[0])),
            ('multiplication', lambda a, b: a * b, (spike, parameters[1])),
            ('sign', sign, (spike,))):
        assertions['commutes_with_' + name] = (
            transpose(pointwise(function, *arguments)) ==
            pointwise(function, *(transpose(a) for a in arguments)))
    if not all(assertions.values()):
        raise AssertionError(assertions)
    print(json.dumps({'spike': spike.description(),
                      'transposed_spike': moved.description(),
                      'finite_example_checks': assertions,
                      'scope': 'Specific witnesses only; see the written universal proof'},
                     indent=2))


if __name__ == '__main__':
    main()
