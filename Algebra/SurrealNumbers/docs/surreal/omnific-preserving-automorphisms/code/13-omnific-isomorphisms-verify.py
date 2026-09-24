#!/usr/bin/env python3
"""Exact finite checks for Automatic Hahn Linearity of Omnific Isomorphisms.

These tests check finite identities and finite models. They do not verify the
infinite-support arguments, class foundations, or theorems in a proof assistant.
Only Python's standard library is required. Run from any working directory.
"""
from __future__ import annotations
import argparse
import json
import random
from fractions import Fraction as Q
from math import comb
from pathlib import Path

checks = 0
categories: dict[str, int] = {}

def check(condition: bool, category: str) -> None:
    global checks
    if not condition:
        raise AssertionError(f"Failed check in {category}")
    checks += 1
    categories[category] = categories.get(category, 0) + 1

# Finite Laurent polynomials with rational coefficients.
def clean(p):
    return {e: c for e, c in p.items() if c}

def add(p, q):
    r = dict(p)
    for e, c in q.items():
        r[e] = r.get(e, Q(0)) + c
    return clean(r)

def mul(p, q):
    r = {}
    for e, a in p.items():
        for f, b in q.items():
            r[e + f] = r.get(e + f, Q(0)) + a * b
    return clean(r)

def ct(p):
    return p.get(0, Q(0))

def pair(p, q):
    return ct(mul(p, q))

def lift(p, d, c):
    return {d * e: a * c**e for e, a in p.items()}

def adjoint(q, d, c):
    return {e // d: a * c**(-e // d) for e, a in q.items() if e % d == 0}

rng = random.Random(20260923)
def rand_laurent():
    return clean({e: Q(rng.randrange(-4, 5), rng.randrange(1, 5))
                  for e in range(-6, 7)})

for _ in range(160):
    p, q, h = rand_laurent(), rand_laurent(), rand_laurent()
    d = rng.randrange(1, 5)
    c = Q(rng.randrange(1, 5), rng.randrange(1, 5))
    check(pair(lift(p, d, c), q) == pair(p, adjoint(q, d, c)),
          'monomial_adjoint')
    check(adjoint(lift(p, d, c), d, c) == p, 'adjoint_retraction')
    check(adjoint(mul(lift(p, d, c), q), d, c) ==
          mul(p, adjoint(q, d, c)), 'frobenius_identity')
    check(lift(mul(p, h), d, c) == mul(lift(p, d, c), lift(h, d, c)),
          'monomial_multiplicativity')
    for e in range(-10, 11):
        check(p.get(e, Q(0)) == pair(p, {-e: Q(1)}),
              'coefficient_reconstruction')

check(adjoint({1: Q(1)}, 2, Q(1)) == {}, 'projection_not_multiplicative')
check(adjoint({-1: Q(1)}, 2, Q(1)) == {}, 'projection_not_multiplicative')
check(adjoint({0: Q(1)}, 2, Q(1)) == {0: Q(1)},
      'projection_not_multiplicative')

# Finite binary gliding-hump construction: the j-th selected row has a fresh
# variable. Later assignments do not change the earlier rows.
for modulus in [2, 3, 5, 7, 11]:
    for repetition in range(30):
        rows = []
        for j in range(24):
            row = {k: rng.randrange(modulus) for k in range(j)}
            row[j] = rng.randrange(1, modulus)
            rows.append({k: a for k, a in row.items() if a})
        values = {}
        for j, row in enumerate(rows):
            before = sum(a * values.get(k, 0) for k, a in row.items()) % modulus
            values[j] = 0 if before else 1
            check(sum(a * values[k] for k, a in row.items()) % modulus != 0,
                  'binary_gliding_hump')
        for row in rows:
            check(sum(a * values[k] for k, a in row.items()) % modulus != 0,
                  'binary_witness_persistence')

# A polynomial in b is represented by {degree: rational coefficient}.
def padd(p, q):
    return add(p, q)

def pmul(p, q):
    return mul(p, q)

def pscale(p, s):
    return clean({d: c * s for d, c in p.items()})

# Input series: {integer exponent: polynomial in b}.
# Output series: {(macro exponent, microscopic exponent): polynomial in b}.
def hadd(f, g):
    r = {e: dict(p) for e, p in f.items()}
    for e, p in g.items():
        r[e] = padd(r.get(e, {}), p)
    return {e: p for e, p in r.items() if p}

def exponent_add(a, b):
    if isinstance(a, tuple):
        return tuple(x + y for x, y in zip(a, b))
    return a + b

def hmul(f, g):
    r = {}
    for e, p in f.items():
        for d, q in g.items():
            h = exponent_add(e, d)
            r[h] = padd(r.get(h, {}), pmul(p, q))
    return {e: p for e, p in r.items() if p}

def drift(f):
    """Exact Taylor map b -> b+u with exponents in Z lex Z."""
    out = {}
    for macro, poly in f.items():
        for degree, a in poly.items():
            for n in range(degree + 1):
                e = (macro, n)
                term = {degree - n: a * comb(degree, n)}
                out[e] = padd(out.get(e, {}), term)
    return {e: p for e, p in out.items() if p}

def rand_hahn():
    f = {}
    for e in range(-3, 4):
        p = clean({d: Q(rng.randrange(-2, 3)) for d in range(5)})
        if p:
            f[e] = p
    return f

for _ in range(120):
    f, g = rand_hahn(), rand_hahn()
    check(drift(hadd(f, g)) == hadd(drift(f), drift(g)), 'drift_additivity')
    check(drift(hmul(f, g)) == hmul(drift(f), drift(g)),
          'drift_multiplicativity')
    check(drift(f).get((0, 0), {}) == f.get(0, {}), 'drift_constant_term')
    check(min(drift(f)) == (min(f), 0), 'drift_leading_exponent')
    integer_part = {e: p for e, p in f.items() if e < 0}
    n = rng.randrange(-10, 11)
    if n:
        integer_part[0] = {0: Q(n)}
    image = drift(integer_part)
    check(all(e < (0, 0) or (e == (0, 0) and set(p) <= {0})
              for e, p in image.items()), 'drift_integer_part')

check(drift({0: {1: Q(1)}}) == {(0, 0): {1: Q(1)}, (0, 1): {0: Q(1)}},
      'drift_moves_coefficient')
check(drift({-1: {0: Q(1)}}) == {(-1, 0): {0: Q(1)}},
      'drift_monomial')

# Finite shadow of the countable residue detector for a descending family.
for n in range(1, 65):
    tester = {j: Q(1) for j in range(1, n + 1)}
    for j in range(1, n + 1):
        check(pair({-j: Q(1)}, tester) == 1, 'descending_support_detector')

report = {
    'title': 'Finite verification for Automatic Hahn Linearity of Omnific Isomorphisms',
    'seed': 20260923,
    'assertions_passed': checks,
    'categories': categories,
    'status': 'all exact finite checks passed',
    'scope': 'Finite identities and finite shadows only; not a proof of infinite/class theorems.',
    'dependencies': 'Python 3 standard library',
}
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path,
                    default=Path(__file__).resolve().parents[1] / 'data' / 'verification.json')
args = parser.parse_args()
args.output.parent.mkdir(parents=True, exist_ok=True)
args.output.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
print(json.dumps(report, indent=2))
