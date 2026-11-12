"""Exact finite representations illustrating the paper's infinite model.

This is an explanatory artifact, not a proof checker and not a test of
unbounded quantified induction. The universal theorem is proved in the paper.
"""
from dataclasses import dataclass
from pathlib import Path
import json


@dataclass(frozen=True)
class EC:
    tail: int
    exceptions: tuple = ()

    @staticmethod
    def make(tail, exceptions=()):
        entries = dict(exceptions)
        if tail < 0 or any(i < 0 or v < 0 for i, v in entries.items()):
            raise ValueError("Natural indices and values are required")
        return EC(tail, tuple(sorted((i, v) for i, v in entries.items()
                                     if v != tail)))

    def at(self, index):
        return dict(self.exceptions).get(index, self.tail)

    def swapped(self, first, second):
        indices = {i for i, _ in self.exceptions} | {first, second}
        def other(i):
            return second if i == first else first if i == second else i
        return EC.make(self.tail, ((i, self.at(other(i))) for i in indices))

    def as_json(self):
        return {"tail": self.tail, "exceptions": [list(item) for item in self.exceptions]}


def pointwise(function, *arguments):
    indices = {i for a in arguments for i, _ in a.exceptions}
    tail = function(*(a.tail for a in arguments))
    return EC.make(tail, ((i, function(*(a.at(i) for a in arguments)))
                          for i in indices))


def pointwise_le(left, right):
    indices = {i for a in (left, right) for i, _ in a.exceptions}
    return left.tail <= right.tail and all(left.at(i) <= right.at(i)
                                          for i in indices)


def has_successor_preimage(value):
    # An eventually constant natural sequence has a predecessor under S
    # exactly when every coordinate is positive. This criterion is exact.
    return value.tail > 0 and all(v > 0 for _, v in value.exceptions)


def examples():
    zero, one = EC.make(0), EC.make(1)
    e = EC.make(0, [(10, 1)])
    f = EC.make(0, [(11, 1)])
    parameters = [EC.make(7, [(0, 2), (4, 9)]), EC.make(0, [(3, 5)])]
    swap = lambda a: a.swapped(10, 11)
    sign_e = pointwise(lambda n: int(n != 0), e)
    samples = [zero, one, e, f] + parameters
    operations = {
        "successor": (lambda a: a + 1, 1),
        "addition": (lambda a, b: a + b, 2),
        "multiplication": (lambda a, b: a * b, 2),
        "sign": (lambda a: int(a != 0), 1),
    }
    checked = {}
    for name, (function, arity) in operations.items():
        import itertools
        checked[name] = all(
            swap(pointwise(function, *args)) ==
            pointwise(function, *(swap(a) for a in args))
            for args in itertools.product(samples, repeat=arity)
        )
    return {
        "scope": "Exact examples in EC(N), not verification of quantified metatheorems",
        "e_i": e.as_json(), "e_j": f.as_json(),
        "parameters": [a.as_json() for a in parameters],
        "parameters_fixed_by_swap": all(swap(a) == a for a in parameters),
        "swap_is_nonidentity": swap(e) == f and e != f,
        "swap_squared_fixes_samples": all(swap(swap(a)) == a for a in samples),
        "sample_operation_equivariance": checked,
        "e_i_is_zero": e == zero,
        "e_i_is_successor": has_successor_preimage(e),
        "sign_e_i_is_zero": sign_e == zero,
        "sign_e_i_is_one": sign_e == one,
        "e_i_le_e_j": pointwise_le(e, f),
        "e_j_le_e_i": pointwise_le(f, e),
    }


if __name__ == "__main__":
    result = examples()
    destination = Path(__file__).resolve().parents[1] / "evidence/model_examples.json"
    destination.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
