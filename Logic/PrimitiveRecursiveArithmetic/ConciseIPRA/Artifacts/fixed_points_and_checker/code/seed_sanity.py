"""Finite sanity checks of the explicit seed, not a proof of the tower.

The seed only interprets successor and the two designated iterators J,K.
The report constructs all remaining iterators by a coherent ultrapower tower.
"""
from itertools import product
from pathlib import Path
import json

ZERO = (0, 0)
ONE = (0, 1)


def good(a):
    q, z = a
    return q > 0 or (q == 0 and z >= 0)


def plus(a, b):
    return a[0] + b[0], a[1] + b[1]


def succ(a):
    return a[0], a[1] + 1


def double_counter(a):
    return a[0], 2 * a[1]


def J(n, a):
    return plus(a, n)


def K(n, a):
    return plus(a, double_counter(n))


def eq_induction_formula(n):
    return K(n, ZERO) == J(n, n)


def main():
    points = [(0, z) for z in range(6)] + list(product(range(1, 4), range(-4, 5)))
    for n, a in product(points, repeat=2):
        assert good(J(n, a)) and good(K(n, a))
        assert J(ZERO, a) == a and K(ZERO, a) == a
        assert J(succ(n), a) == succ(J(n, a))
        assert K(succ(n), a) == succ(succ(K(n, a)))
        assert J(n, ZERO) == n
        assert J(n, succ(a)) == succ(J(n, a))
        assert K(n, succ(succ(a))) == succ(succ(K(n, a)))
        assert plus(n, a) == plus(a, n)
        assert succ(n) != n and succ(succ(n)) != n
        assert (succ(n) == succ(a)) == (n == a)
        assert not (succ(n) == ZERO)
    for a, b, c in product(points, repeat=3):
        assert plus(plus(a, b), c) == plus(a, plus(b, c))
        assert (plus(a, c) == plus(b, c)) == (a == b)
    assert eq_induction_formula(ZERO)
    for n in points:
        assert not eq_induction_formula(n) or eq_induction_formula(succ(n))
        if n[0]:
            assert not eq_induction_formula(n)
            assert good((n[0], n[1]-1))
        elif n[1]:
            assert good((0, n[1]-1))
    c = (1, 0)
    result = {
        'points': len(points), 'ordered_pairs': len(points)**2,
        'ordered_triples': len(points)**3,
        'counterexample_counter': c,
        'K_c_zero': K(c, ZERO), 'J_c_c': J(c, c),
        'finite_seed_checks_passed': True,
        'infinite_tower_verified_by_this_script': False,
        'all_native_bodies_implemented_by_this_script': False,
    }
    dest = Path(__file__).resolve().parents[1]/'evidence'/'seed_sanity.json'
    dest.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
