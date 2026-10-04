#!/usr/bin/env python3
"""Exact finite checks for 'Borel Presentations and Support Barriers'.

Python 3.10+, standard library only.  These checks are not a verification of
infinite well-foundedness, descriptive completeness, or Glazer's theorem.
Run: python verify.py --output verification.json
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
from fractions import Fraction as F
import json
import platform
import random
from typing import Iterable


@dataclass(frozen=True)
class Poly:
    """Finite rational Puiseux expression in a positive infinite variable X."""
    terms: tuple[tuple[F, F], ...]

    @staticmethod
    def make(items: Iterable[tuple[F | int, F | int]]) -> 'Poly':
        d: dict[F, F] = {}
        for q, a in items:
            q, a = F(q), F(a)
            d[q] = d.get(q, F(0)) + a
        return Poly(tuple(sorted((q, a) for q, a in d.items() if a)))

    def __add__(self, other: 'Poly') -> 'Poly':
        return Poly.make(self.terms + other.terms)

    def __neg__(self) -> 'Poly':
        return Poly.make((q, -a) for q, a in self.terms)

    def __sub__(self, other: 'Poly') -> 'Poly':
        return self + (-other)

    def __mul__(self, other: 'Poly') -> 'Poly':
        return Poly.make((p + q, a * b) for p, a in self.terms
                         for q, b in other.terms)

    def coefficient(self, q: F | int) -> F:
        return dict(self.terms).get(F(q), F(0))

    def sign(self) -> int:
        if not self.terms:
            return 0
        a = self.terms[-1][1]
        return 1 if a > 0 else -1

    def positive_support(self) -> frozenset[F]:
        return frozenset(q for q, _ in self.terms if q > 0)

    def in_integer_part(self) -> bool:
        return all(q >= 0 for q, _ in self.terms) and self.coefficient(0).denominator == 1

    def integer_part(self) -> 'Poly':
        """Exact floor into Z + finite positive-power principal parts."""
        principal = [(q, a) for q, a in self.terms if q > 0]
        r = self.coefficient(0)
        n = r.numerator // r.denominator
        tail = Poly.make((q, a) for q, a in self.terms if q < 0)
        if r.denominator == 1 and tail.sign() < 0:
            n -= 1
        return Poly.make(principal + [(F(0), F(n))])


ZERO = Poly.make([])
ONE = Poly.make([(0, 1)])
X = Poly.make([(1, 1)])
COUNTS: dict[str, int] = {}


def check(group: str, statement: bool) -> None:
    if not statement:
        raise AssertionError(f'Check failed in group: {group}')
    COUNTS[group] = COUNTS.get(group, 0) + 1


def random_poly(rng: random.Random, exponents: tuple[F, ...],
                integer_constant: bool = True) -> Poly:
    items = []
    for q in exponents:
        if rng.randrange(3):
            den = 1 if q == 0 and integer_constant else rng.randint(1, 5)
            items.append((q, F(rng.randint(-5, 5), den)))
    return Poly.make(items)


def kb_cmp(s: tuple[int, ...], t: tuple[int, ...]) -> int:
    """Kleene--Brouwer: extensions precede their proper prefixes."""
    for a, b in zip(s, t):
        if a != b:
            return -1 if a < b else 1
    if len(s) == len(t):
        return 0
    return -1 if len(s) > len(t) else 1


def nodes_of_weight(w: int) -> list[tuple[int, ...]]:
    if w == 0:
        return [()]
    return [(a,) + tail for a in range(w)
            for tail in nodes_of_weight(w - a - 1)]


def finite_kb_embedding(weight: int) -> dict[tuple[int, ...], F]:
    """Initial segment of one fixed enumeration and its midpoint embedding.

    e reverses KB and takes values in (1/3, 2/3). Increasing weight gives a
    coherent extension, not a fresh embedding of each finite tree.
    """
    h: dict[tuple[int, ...], F] = {}
    for w in range(weight + 1):
        for s in nodes_of_weight(w):
            lo = max([F(0)] + [v for t, v in h.items() if kb_cmp(t, s) < 0])
            hi = min([F(1)] + [v for t, v in h.items() if kb_cmp(s, t) < 0])
            h[s] = (lo + hi) / 2
    return {s: F(2, 3) - v / 3 for s, v in h.items()}


def run() -> dict:
    rng = random.Random(2601003)
    exps = tuple(map(F, [0, F(1, 4), F(1, 3), F(1, 2), 1, F(3, 2), 2]))
    for _ in range(1000):
        a, b, c = [random_poly(rng, exps) for _ in range(3)]
        check('ring_laws', (a + b) + c == a + (b + c))
        check('ring_laws', a + b == b + a)
        check('ring_laws', (a * b) * c == a * (b * c))
        check('ring_laws', a * b == b * a)
        check('ring_laws', a * (b + c) == a * b + a * c)
        check('ring_laws', a + (-a) == ZERO and a * ONE == a)
        check('integer_part_closure', (a + b).in_integer_part())
        check('integer_part_closure', (a * b).in_integer_part())
        ap = a if a.sign() >= 0 else -a
        bp = b if b.sign() >= 0 else -b
        check('positive_cone', (ap + bp).sign() >= 0)
        check('positive_cone', (ap * bp).sign() >= 0)
        if ap.sign() > 0:
            check('discreteness', (ap - ONE).sign() >= 0)

    all_exps = tuple(map(F, [-2, F(-3, 2), -1, F(-1, 2),
                            0, F(1, 3), 1, F(3, 2), 2]))
    for _ in range(2500):
        f = random_poly(rng, all_exps, integer_constant=False)
        a = f.integer_part()
        check('floor_interval', a.in_integer_part())
        check('floor_interval', (f - a).sign() >= 0)
        check('floor_interval', (ONE - (f - a)).sign() > 0)
    for n in range(-10, 11):
        for q in [F(-1), F(-1, 3), F(-2, 5)]:
            f = Poly.make([(0, n), (q, -1)])
            check('negative_infinitesimal_boundary', f.integer_part() == Poly.make([(0, n - 1)]))

    for delta in [F(0), F(1, 10), F(-1, 10), F(1, 1000), F(-1, 1000)]:
        a = Poly.make([(2, 1), (1, 1)])
        b = Poly.make([(2, 1), (1, -1 + delta)])
        check('addition_cancellation', (a + b).coefficient(1) == delta)
        check('addition_cancellation', (F(1) in (a + b).positive_support()) == (delta != 0))
        a, b = X + ONE, Poly.make([(1, 1 + delta), (0, -1)])
        check('multiplication_cancellation', (a * b).coefficient(1) == delta)
        check('multiplication_cancellation', (F(1) in (a * b).positive_support()) == (delta != 0))
        check('multiplication_cancellation', a.sign() > 0 and b.sign() > 0)

    e = finite_kb_embedding(8)
    for s, v in e.items():
        check('KB_embedding', F(1, 3) < v < F(2, 3))
        for t, w in e.items():
            check('KB_embedding', (kb_cmp(s, t) < 0) == (v > w))
    earlier = finite_kb_embedding(7)
    check('KB_coherence', all(e[s] == v for s, v in earlier.items()))
    for n in range(8):
        check('branch_approximants', e[(0,) * n] < e[(0,) * (n + 1)])

    return {
        'status': 'PASS',
        'seed': 2601003,
        'python': platform.python_version(),
        'assertions': sum(COUNTS.values()),
        'groups': COUNTS,
        'KB_nodes': len(e),
        'scope': 'Finite exact-rational checks only; not a formal proof of the infinitary theorems.'
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', help='Optional path for the JSON result')
    args = parser.parse_args()
    result = run()
    text = json.dumps(result, indent=2, sort_keys=True)
    print(text)
    if args.output:
        with open(args.output, 'w', encoding='utf-8') as out:
            out.write(text + '\n')


if __name__ == '__main__':
    main()
