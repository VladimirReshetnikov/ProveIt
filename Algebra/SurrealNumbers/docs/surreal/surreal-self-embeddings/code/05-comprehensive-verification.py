#!/usr/bin/env python3
"""Exact finite regression checks for Self-Embeddings of the Surreal Numbers.

Python 3.10+; standard library only. No floating-point arithmetic is used.
These are finite algebraic and sign-word checks, NOT a formal verification
of arbitrary ordinals, class recursion, Hahn summability, or limits.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
import random
from collections import Counter
from fractions import Fraction as F
from functools import cmp_to_key
from pathlib import Path
from typing import Callable, TypeAlias

Vec: TypeAlias = tuple[tuple[F, F], ...]
Outer: TypeAlias = dict[Vec, F]
Word: TypeAlias = tuple[int, ...]
Poly: TypeAlias = dict[tuple[int, ...], F]
ZERO: Vec = ()
COUNTS: Counter[str] = Counter()


def check(group: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(f"Check failed in {group}, after {COUNTS[group]} passes")
    COUNTS[group] += 1


def canon(items) -> Vec:
    out: dict[F, F] = {}
    for exponent, coefficient in items:
        a, c = F(exponent), F(coefficient)
        out[a] = out.get(a, F(0)) + c
    return tuple(sorted((a, c) for a, c in out.items() if c))


def vadd(x: Vec, y: Vec) -> Vec:
    return canon((*x, *y))


def vscale(x: Vec, r: F) -> Vec:
    return canon((a, r * c) for a, c in x)


def vcmp(x: Vec, y: Vec) -> int:
    delta = vadd(x, vscale(y, F(-1)))
    return 0 if not delta else (1 if delta[-1][1] > 0 else -1)


def lift(f: Callable[[F], F], x: Vec) -> Vec:
    return canon((f(a), c) for a, c in x)


def compression(a: F) -> F:
    return a / (1 + abs(a))


def ordinal_fixer(a: F) -> F:
    return a if a >= 0 else a / (1 - a)


def oclean(x: Outer) -> Outer:
    return {a: F(c) for a, c in x.items() if c}


def oadd(x: Outer, y: Outer) -> Outer:
    out = dict(x)
    for a, c in y.items():
        out[a] = out.get(a, F(0)) + c
    return oclean(out)


def omult(x: Outer, y: Outer) -> Outer:
    out: Outer = {}
    for a, c in x.items():
        for b, d in y.items():
            t = vadd(a, b)
            out[t] = out.get(t, F(0)) + c * d
    return oclean(out)


def hahn(phi: Callable[[Vec], Vec], character: Callable[[Vec], F], x: Outer) -> Outer:
    out: Outer = {}
    for a, c in x.items():
        key = phi(a)
        out[key] = out.get(key, F(0)) + c * character(a)
    return oclean(out)


def double_lift(f: Callable[[F], F], x: Outer) -> Outer:
    return hahn(lambda a: lift(f, a), lambda _: F(1), x)


def osign(x: Outer) -> int:
    if not x:
        return 0
    lead = max(x, key=cmp_to_key(vcmp))
    return 1 if x[lead] > 0 else -1


def omnific(x: Outer) -> bool:
    return all(vcmp(a, ZERO) >= 0 for a in x) and x.get(ZERO, F(0)).denominator == 1


def word_cmp(x: Word, y: Word) -> int:
    for a, b in itertools.zip_longest(x, y, fillvalue=0):
        if a != b:
            return 1 if a > b else -1
    return 0


def prefix(x: Word, y: Word) -> bool:
    return len(x) <= len(y) and y[:len(x)] == x


def meet(x: Word, y: Word) -> Word:
    n = 0
    while n < min(len(x), len(y)) and x[n] == y[n]:
        n += 1
    return x[:n]


def random_vec(rng: random.Random) -> Vec:
    return canon((F(rng.randrange(-5, 6), rng.randrange(1, 4)), F(rng.randrange(-3, 4)))
                 for _ in range(rng.randrange(1, 5)))


def random_outer(rng: random.Random) -> Outer:
    out: Outer = {}
    for _ in range(rng.randrange(1, 5)):
        key = random_vec(rng)
        out[key] = out.get(key, F(0)) + F(rng.randrange(-4, 5), rng.randrange(1, 4))
    return oclean(out)


def character(a: Vec) -> F:
    value = dict(a).get(F(-1), F(0))
    if value.denominator != 1:
        raise ValueError("This exact test character requires integral selected coefficients")
    return F(2) ** value.numerator


def padd(x: Poly, y: Poly) -> Poly:
    out = dict(x)
    for a, c in y.items():
        out[a] = out.get(a, F(0)) + c
    return {a: c for a, c in out.items() if c}


def pneg(x: Poly) -> Poly:
    return {a: -c for a, c in x.items()}


def psub(x: Poly, y: Poly) -> Poly:
    return padd(x, pneg(y))


def pmul(x: Poly, y: Poly) -> Poly:
    out: Poly = {}
    for a, c in x.items():
        for b, d in y.items():
            key = tuple(i + j for i, j in zip(a, b))
            out[key] = out.get(key, F(0)) + c * d
    return {a: c for a, c in out.items() if c}


def variable(i: int) -> Poly:
    return {tuple(int(j == i) for j in range(6)): F(1)}


def run(seed: int) -> dict:
    COUNTS.clear()
    rng = random.Random(seed)
    words = [w for n in range(7) for w in itertools.product((-1, 1), repeat=n)]

    def padding(w: Word) -> Word:
        result = (1,)
        for i, sign in enumerate(w):
            # A successor block always begins with the required sign.
            result += (sign,) + ((-sign, sign) if i % 2 else (sign,))
        return result

    maps = [lambda w: (1, -1) + w,
            lambda w: tuple(a for sign in w for a in (sign, sign)), padding]
    for e in maps:
        image = {w: e(w) for w in words}
        for x, y in itertools.product(words, repeat=2):
            ex, ey = image[x], image[y]
            check('finite_tree_order', word_cmp(x, y) == word_cmp(ex, ey))
            check('finite_tree_prefix', prefix(x, y) == prefix(ex, ey))
            check('finite_tree_meet', meet(ex, ey) == image[meet(x, y)])

    grid = sorted({F(a, b) for a in range(-12, 13) for b in range(1, 5)})
    for x in grid:
        cx = compression(x)
        check('rational_compression', -1 < cx < 1 and cx / (1 - abs(cx)) == x)
        check('rational_ordinal_fixer', ordinal_fixer(x) > -1)
    for x, y in zip(grid, grid[1:]):
        check('rational_compression_order', compression(x) < compression(y))
        check('rational_ordinal_fixer_order', ordinal_fixer(x) < ordinal_fixer(y))

    f, g = compression, ordinal_fixer
    for _ in range(90):
        a, b = random_vec(rng), random_vec(rng)
        check('first_lift_addition', lift(f, vadd(a, b)) == vadd(lift(f, a), lift(f, b)))
        check('first_lift_order', vcmp(a, b) == vcmp(lift(f, a), lift(f, b)))
        check('first_lift_composition', lift(f, lift(g, a)) == lift(lambda t: f(g(t)), a))
        x, y = random_outer(rng), random_outer(rng)
        ex, ey = double_lift(f, x), double_lift(f, y)
        check('double_lift_addition', double_lift(f, oadd(x, y)) == oadd(ex, ey))
        check('double_lift_multiplication', double_lift(f, omult(x, y)) == omult(ex, ey))
        check('double_lift_composition', double_lift(f, double_lift(g, x)) ==
              double_lift(lambda t: f(g(t)), x))
        check('double_lift_order', osign(x) == osign(ex))
        check('double_lift_omnific', omnific(x) == omnific(ex))
        phi = lambda v: vscale(v, F(2))
        psi = lambda v: vscale(v, F(3))
        hx = hahn(phi, character, x)
        hy = hahn(phi, character, y)
        check('weighted_multiplication', hahn(phi, character, omult(x, y)) == omult(hx, hy))
        left = hahn(phi, character, hahn(psi, character, x))
        right = hahn(lambda v: phi(psi(v)), lambda v: character(v) * character(psi(v)), x)
        check('weighted_composition', left == right)
        check('weighted_omnific', omnific(hx) == omnific(x))
        check('weighted_character', character(vadd(a, b)) == character(a) * character(b))

    one: Outer = {ZERO: F(1)}
    check('unit', double_lift(f, one) == one)
    # A single lift is not generally multiplicative: C(2) != C(1)+C(1).
    check('one_level_counterexample', compression(F(2)) != 2 * compression(F(1)))
    inner_omega_inverse = canon([(F(-1), F(1))])
    nested = {inner_omega_inverse: F(1)}
    expected = {canon([(F(-1, 2), F(1))]): F(1)}
    check('nested_monomial_witness', double_lift(g, nested) == expected)

    a, b, sa, sb, ta, tb = (variable(i) for i in range(6))
    lhs = psub(pmul(sa, sb), pmul(a, b))
    correct = padd(pmul(sa, psub(sb, b)), pmul(b, psub(sa, a)))
    incorrect = padd(pmul(a, psub(sb, b)), pmul(b, psub(sa, a)))
    check('symbolic_twisted_product', lhs == correct)
    check('symbolic_untwisted_counterexample', lhs != incorrect)
    two_lhs = psub(pmul(sa, sb), pmul(ta, tb))
    two_rhs = padd(pmul(sa, psub(sb, tb)), pmul(tb, psub(sa, ta)))
    check('symbolic_two_map_product', two_lhs == two_rhs)

    for q in [F(2), F(3, 2), F(1, 2), F(1, 3)]:
        for n in range(1, 31):
            exponent = -F(n)
            check('dilation_leading_exponent', q * exponent - exponent == (q - 1) * exponent)
            check('dilation_sign', ((q - 1) * exponent < 0) == (q > 1))
    for m, d in itertools.product(range(13), repeat=2):
        n = max(m + 2, d + 2)
        check('lacunary_degree_gap', math.factorial(n + 1) > m + d * math.factorial(n))

    return {
        'status': 'PASS', 'seed': seed,
        'arithmetic': 'exact fractions; symbolic sparse polynomials; no floats',
        'total_assertions': sum(COUNTS.values()), 'groups': dict(sorted(COUNTS.items())),
        'finite_word_max_length': 6, 'random_hahn_pairs': 90,
        'counterexample': {'one_level_f_2': str(compression(F(2))),
                           'two_times_f_1': str(2 * compression(F(1)))},
        'limitations': [
            'Finite sign words do not certify arbitrary ordinal successor/limit recursion.',
            'Finite convolutions do not certify infinite Hahn support and summability theorems.',
            'Leading-exponent tests do not certify epsilon-delta limits on the full surreal class.',
            'No class existence, elementary-embedding construction, or truth principle is tested.',
            'No Lean or other proof-assistant verification is claimed.'
        ]
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seed', type=int, default=20261003)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('verification.json'))
    args = parser.parse_args()
    report = run(args.seed)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
