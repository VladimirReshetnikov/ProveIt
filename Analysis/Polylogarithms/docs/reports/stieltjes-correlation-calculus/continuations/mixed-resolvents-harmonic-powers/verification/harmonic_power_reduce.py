"""Exact finite normal form for FP integral_0^1 psi(x)^k dx.

Theorem hp:allpowers in higher_digamma.tex proves this algorithm.
Output: B_k - C_k + [u] E_k(u).  Every coefficient is symbolic and exact.
Convergent MZVs of weight <= 5 use the explicitly documented classical
table. Higher weights remain named Z_a_b_... symbols; there is no
claim of minimality. No numerical fit is used.

Usage: python harmonic_power_reduce.py 5 --output power5.json
Requires Python 3 and SymPy. No network or file access beyond --output.
"""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from functools import lru_cache
from pathlib import Path

import sympy as s


@lru_cache(None)
def stuffle(u: tuple[int, ...], v: tuple[int, ...]):
    """Immutable exact strict quasi-shuffle, including multiplicities."""
    if not u:
        return ((v, 1),)
    if not v:
        return ((u, 1),)
    out = defaultdict(int)
    for w, c in stuffle(u[1:], v):
        out[(u[0],) + w] += c
    for w, c in stuffle(u, v[1:]):
        out[(v[0],) + w] += c
    for w, c in stuffle(u[1:], v[1:]):
        out[(u[0] + v[0],) + w] += c
    return tuple(sorted(out.items()))


class PowerReduction:
    def __init__(self, k: int):
        if k < 1:
            raise ValueError("k must be positive")
        self.k = k
        self.g = s.Symbol("gamma")
        self.T = s.Symbol("T")
        self.H = s.symbols("H1:" + str(k + 1))
        self.z = {j: s.Symbol("zeta" + str(j)) for j in range(2, max(k, 5) + 1)}
        z2, z3, z4, z5 = (self.z[j] for j in range(2, 6))
        self.table = {
            (2, 1): z3,
            (3, 1): z4 / 4,
            (2, 2): 3 * z4 / 4,
            (2, 1, 1): z4,
            (4, 1): 2 * z5 - z2 * z3,
            (3, 2): 3 * z2 * z3 - s.Rational(11, 2) * z5,
            (2, 3): s.Rational(9, 2) * z5 - 2 * z2 * z3,
            (3, 1, 1): 2 * z5 - z2 * z3,
            (2, 2, 1): 3 * z2 * z3 - s.Rational(11, 2) * z5,
            (2, 1, 2): s.Rational(9, 2) * z5 - 2 * z2 * z3,
            (2, 1, 1, 1): z5,
        }

    def simplify(self, expression):
        return s.expand(s.expand(expression).subs(self.z[2] ** 2, s.Rational(5, 2) * self.z[4]))

    def zword(self, word):
        if len(word) == 1:
            return self.z.get(word[0], s.Symbol("zeta" + str(word[0])))
        return self.table.get(word, s.Symbol("Z_" + "_".join(map(str, word))))

    @lru_cache(None)
    def regularize(self, word):
        if not word:
            return s.S(1)
        if word == (1,):
            return self.T
        if word[0] >= 2:
            return self.zword(word)
        terms = dict(stuffle((1,), word[1:]))
        multiplicity = terms.pop(word)
        return s.expand(
            (self.T * self.regularize(word[1:])
             - sum(c * self.regularize(w) for w, c in terms.items()))
            / multiplicity
        )

    def poly_words(self, expression):
        out = defaultdict(lambda: s.S(0))
        for powers, coefficient in s.Poly(s.expand(expression), *self.H).terms():
            words = {(): coefficient}
            for i, exponent in enumerate(powers):
                for _ in range(exponent):
                    new = defaultdict(lambda: s.S(0))
                    for w, c in words.items():
                        for v, multiplier in stuffle(w, (i + 1,)):
                            new[v] += c * multiplier
                    words = dict(new)
            for w, c in words.items():
                out[w] += c
        return {w: s.expand(c) for w, c in out.items() if c != 0}

    def sum_poly(self, expression, outer, previous=False):
        out = s.S(0)
        for word, coefficient in self.poly_words(expression).items():
            out += coefficient * self.regularize((outer,) + word)
            if word and not previous:
                out += coefficient * self.regularize((outer + word[0],) + word[1:])
        return s.expand(out)

    def delta(self, expression):
        x = s.Symbol("x")
        shift = {h: h + x ** (j + 1) for j, h in enumerate(self.H)}
        difference = s.expand(expression.subs(shift, simultaneous=True) - expression)
        return tuple((power[0], c) for power, c in s.Poly(difference, x).terms() if c != 0)

    def run(self):
        # Multiply truncated coefficient vectors, retaining powers 0,...,k.
        V = [-s.S(1), self.H[0] - self.g]
        V += [self.H[j - 1] + (-1) ** j * self.z[j] for j in range(2, self.k + 1)]
        coefficients = [s.S(1)]
        for _ in range(self.k):
            new = [s.S(0)] * min(self.k + 1, len(coefficients) + len(V) - 1)
            for i, c in enumerate(coefficients):
                for j, v in enumerate(V[: len(new) - i]):
                    new[i + j] += c * v
            coefficients = [s.expand(c) for c in new]
        self.p = {j: coefficients[self.k - j] for j in range(1, self.k + 1)}
        self.kappa = coefficients[self.k].subs({h: 0 for h in self.H})
        self.B = self.kappa
        for j in range(2, self.k + 1):
            for m, coefficient in self.delta(self.p[j]):
                self.B += self.sum_poly(coefficient, j - 1 + m, previous=True) / (j - 1)
            self.B -= self.sum_poly(self.p[j], j)
        self.C = self.sum_poly(self.p[1], 1).subs(self.T, self.g)
        self.B = self.simplify(self.B)
        self.C = self.simplify(self.C)
        self.E = defaultdict(lambda: s.S(0))
        for m, coefficient in self.delta(self.p[1]):
            for word, c in self.poly_words(coefficient).items():
                self.E[(m,) + word] += c
        self.E = {w: self.simplify(c) for w, c in self.E.items() if c != 0}
        return self

    def to_dict(self):
        return {
            "k": self.k,
            "formula": "Q_k = B_k - C_k + [u^1] E_k(u)",
            "coefficient_semantics": "Laurent coefficient in u, no extra factorial or sign",
            "harmonic_convention": "strict, descending indices; H_n(r)=sum_{j=1}^n j^(-r)",
            "poles": {str(j): str(c) for j, c in self.p.items()},
            "kappa": str(self.kappa),
            "B": str(self.B),
            "C": str(self.C),
            "B_minus_C": str(self.simplify(self.B - self.C)),
            "E": [{"indices": list(w), "shift_outer_by": "u", "coefficient": str(c)}
                  for w, c in sorted(self.E.items())],
            "status": "exact symbolic algorithm; no arithmetic independence or minimality claim",
        }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("k", type=int)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = json.dumps(PowerReduction(args.k).run().to_dict(), indent=2) + "\n"
    if args.output:
        args.output.write_text(result, encoding="utf-8")
    else:
        print(result, end="")


if __name__ == "__main__":
    main()
