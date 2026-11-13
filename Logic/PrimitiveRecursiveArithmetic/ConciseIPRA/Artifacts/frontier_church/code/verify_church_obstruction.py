"""Finite checks for the self-contained Church-numeral obstruction note.

No claim to verify all simply typed terms or an infinite family of models.
"""
from itertools import product
from math import lcm
import json


def powers(mapping, exponent):
    out = list(range(len(mapping)))
    for _ in range(exponent):
        out = [mapping[x] for x in out]
    return tuple(out)


def numeral(q, exponent):
    return tuple(powers(f, exponent) for f in product(range(q), repeat=q))


def main():
    if not __debug__:
        raise RuntimeError('Run without -O or -OO')
    ground = [numeral(2, n) for n in range(10)]
    assert len(set(ground)) == 3
    assert all(ground[n] == ground[1 + (n - 1) % 2] for n in range(1, 10))
    assert ground[1] == ground[3]
    assert ground[0] != ground[2]
    successor = (1, 2, 1)
    assert 0 not in successor
    assert all(x == 0 or x in successor for x in range(3))
    endomaps = [{"map": f, "powers_0_1_2_3": [powers(f, n) for n in range(4)]}
                for f in product(range(2), repeat=2)]
    predicates = []
    for characteristic in product((False, True), repeat=3):
        closed = all(not characteristic[x] or characteristic[successor[x]]
                     for x in range(3))
        assert not (characteristic[0] and closed) or all(characteristic)
        predicates.append({"subset": [x for x in range(3) if characteristic[x]],
                           "base_holds": characteristic[0],
                           "step_holds": closed,
                           "conclusion_holds": all(characteristic),
                           "induction_instance_holds":
                               not (characteristic[0] and closed)
                               or all(characteristic)})
    general = []
    for q in range(2, 6):
        period = lcm(*range(1, q + 1))
        count = 0
        for f in product(range(q), repeat=q):
            assert powers(f, q - 1) == powers(f, q - 1 + period)
            count += 1
        chain = tuple(min(i + 1, q - 1) for i in range(q))
        assert powers(chain, q - 2)[0] == q - 2
        assert powers(chain, q - 2 + period)[0] == q - 1
        general.append({"q": q, "lcm": period, "endomaps_checked": count})
    print(json.dumps({"status": "PASS", "numerical_domain_size": 3,
                      "successor": successor,
                      "ground_endomaps": endomaps,
                      "all_subsets_checked_for_induction": predicates,
                      "generalized_finite_examples": general}, indent=2))


if __name__ == "__main__":
    main()
