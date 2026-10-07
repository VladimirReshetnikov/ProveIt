#!/usr/bin/env python3
"""Finite checks for the odd-order rigidity calculation; standard Python only.

The proof is in the article's odd-order rigidity section. These checks verify
the exact qutrit cube counts, two-state coefficients, and random instances
of the exact Weyl-coset expansion and explicit envelope.
"""
from collections import Counter
from itertools import product
from cmath import exp, pi
from math import sqrt
from random import Random
from pathlib import Path
import json


def cube_counts(p, allowed):
    counts = Counter()
    for x, h, k, l in product(range(p), repeat=4):
        vals = [(x+i*h+j*k+r*l) % p
                for i, j, r in product(range(2), repeat=3)]
        if set(vals) <= set(allowed):
            counts[vals.count(0)] += 1
    return counts


def ambiguity(v):
    n = len(v)
    return [[sum(v[x] * v[(x-h) % n].conjugate()
                 * exp(-2j*pi*r*x/n) for x in range(n))
             for r in range(n)] for h in range(n)]


def norm8(v):
    return sum(abs(z)**4 for row in ambiguity(v) for z in row) / len(v)


def verify_expansion(n, rng):
    # Coordinate coefficients are in an orthonormal point-mass basis.
    w = [0j] + [complex(rng.gauss(0, 1), rng.gauss(0, 1))
                for _ in range(n-1)]
    scale = sqrt(sum(abs(z)**2 for z in w))
    w = [z / scale for z in w]
    s = [abs(z)**2 for z in w]
    A = sum(x*x for x in s)
    B = sum(s[x]*s[-x % n] for x in range(n))
    C = sum(s[x]*s[y]*s[(x+y) % n]
            for x, y in product(range(n), repeat=2))
    wd = ambiguity(w)
    ls = [[w[h] * exp(-2j*pi*r*h/n) + w[-h % n].conjugate()
           for r in range(n)] for h in range(n)]
    l4 = sum(abs(ls[h][r])**4 for h in range(1, n)
             for r in range(n)) / n
    assert abs(l4 - (2*A+4*B)) < 1e-10
    K = 4 * sum((abs(ls[h][r])**2 * ls[h][r]
                 * wd[h][r].conjugate()).real
                for h in range(1, n) for r in range(n)) / n
    J = 4*C + sum(2*abs(ls[h][r])**2*abs(wd[h][r])**2
                   + 4*(ls[h][r]*wd[h][r].conjugate()).real**2
                   for h in range(1, n) for r in range(n)) / n
    M = 4 * sum((abs(wd[h][r])**2 * ls[h][r]
                 * wd[h][r].conjugate()).real
                for h in range(1, n) for r in range(n)) / n
    t = rng.random()/6
    F = 1-t
    v = [sqrt(F)] + [sqrt(t)*z for z in w[1:]]
    kappa = norm8(v)
    expansion = (F**4 + 6*F**2*t**2*(A+B)
                 + F**1.5*t**2.5*K + F*t**3*J
                 + F**0.5*t**3.5*M + t**4*norm8(w))
    assert abs(kappa-expansion) < 1e-10, (n, kappa, expansion)
    envelope = F**4 + 6*F**2*t**2 + 104*F*t**3 + t**4
    if n % 3 == 0:
        envelope += 2*sqrt(2)*F**1.5*t**2.5
    assert kappa <= envelope + 1e-10
    return abs(kappa-expansion)


def main():
    counts3 = cube_counts(3, {0, 1, 2})
    assert counts3 == Counter({0: 8, 2: 32, 3: 16, 4: 24, 8: 1})
    counts5 = cube_counts(5, {0, 1})
    assert counts5 == Counter({0: 1, 4: 6, 8: 1})
    for t in (0.001, 0.01, 0.05, 1/6):
        F = 1-t
        v = [sqrt(F), sqrt(t/2), sqrt(t/2)]
        expected = (F**4+6*F**2*t*t+2*sqrt(2)*F**1.5*t**2.5
                    +4*F*t**3+t**4/2)
        assert abs(norm8(v)-expected) < 1e-12
    rng = Random(20261006)
    errors = [verify_expansion(n, rng)
              for n in (3, 5, 7, 9, 15, 25) for _ in range(20)]
    result = {
        'status': 'passed',
        'scope': ('Exact finite cube multiplicities and floating-point checks '
                  'of the analytically proved Weyl expansion and envelope; '
                  'not a formal proof certificate.'),
        'qutrit_cube_counts': dict(sorted(counts3.items())),
        'five_element_two_state_counts': dict(sorted(counts5.items())),
        'qutrit_exact_formula_sample_count': 4,
        'random_seed': 20261006,
        'cyclic_group_orders': [3, 5, 7, 9, 15, 25],
        'random_cases_per_group': 20,
        'random_case_count': len(errors),
        'maximum_expansion_residual': max(errors),
        'expansion_tolerance': 1e-10,
    }
    result_path = (Path(__file__).resolve().parents[1]
                   / 'data' / 'odd_rigidity_checks.json')
    result_path.parent.mkdir(parents=True, exist_ok=True)
    result_path.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n',
                           encoding='utf-8')
    print('Exact qutrit cube counts:', dict(sorted(counts3.items())))
    print('Exact five-element two-state counts:', dict(sorted(counts5.items())))
    print('Random exact-expansion/envelope cases:', len(errors))
    print('Maximum floating expansion residual:', max(errors))
    print('Result file:', result_path)
    print('All checks passed.')


if __name__ == '__main__':
    main()
