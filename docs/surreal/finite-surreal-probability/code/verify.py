#!/usr/bin/env python3
"""Exact finite checks for Surreal Probability and Log-Odds.

Python 3.10+, standard library only.  Rational functions in Q(t) are
ordered at a positive infinitesimal t by their first nonzero coefficient.
This is NOT an implementation of arbitrary surreal numbers, exponential,
infinite summation, measure extension, or a proof assistant.
"""
from __future__ import annotations

import argparse
import json
import math
import platform
import random
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
from typing import Iterable

Poly = tuple[F, ...]


def trim(a: Iterable[F | int]) -> Poly:
    r = [F(x) for x in a]
    while len(r) > 1 and r[-1] == 0:
        r.pop()
    return tuple(r) if r else (F(0),)


def padd(a: Poly, b: Poly) -> Poly:
    return trim((a[i] if i < len(a) else 0) +
                (b[i] if i < len(b) else 0)
                for i in range(max(len(a), len(b))))


def pneg(a: Poly) -> Poly:
    return tuple(-x for x in a)


def pmul(a: Poly, b: Poly) -> Poly:
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return trim(out)


def pdivmod(a: Poly, b: Poly) -> tuple[Poly, Poly]:
    if b == (F(0),):
        raise ZeroDivisionError("zero polynomial divisor")
    rem = list(a)
    quot = [F(0)] * max(1, len(a) - len(b) + 1)
    while tuple(rem) != (F(0),) and len(rem) >= len(b):
        d = len(rem) - len(b)
        c = rem[-1] / b[-1]
        quot[d] += c
        for i, x in enumerate(b):
            rem[i + d] -= c * x
        rem = list(trim(rem))
    return trim(quot), trim(rem)


def pgcd(a: Poly, b: Poly) -> Poly:
    while b != (F(0),):
        _, r = pdivmod(a, b)
        a, b = b, r
    if a == (F(0),):
        return (F(1),)
    return trim(x / a[-1] for x in a)


def order(a: Poly) -> int:
    for i, x in enumerate(a):
        if x:
            return i
    raise ValueError("zero polynomial has no finite order")


@dataclass(frozen=True, init=False)
class Rat:
    num: Poly
    den: Poly

    def __init__(self, num: Iterable[F | int] | F | int = 0,
                 den: Iterable[F | int] | F | int = 1):
        n = trim((num,)) if isinstance(num, (int, F)) else trim(num)
        d = trim((den,)) if isinstance(den, (int, F)) else trim(den)
        if d == (F(0),):
            raise ZeroDivisionError("zero rational-function denominator")
        if n == (F(0),):
            n, d = (F(0),), (F(1),)
        else:
            g = pgcd(n, d)
            n, nr = pdivmod(n, g)
            d, dr = pdivmod(d, g)
            if nr != (F(0),) or dr != (F(0),):
                raise ArithmeticError("nonexact polynomial gcd division")
            c = d[-1]
            n, d = trim(x / c for x in n), trim(x / c for x in d)
        object.__setattr__(self, "num", n)
        object.__setattr__(self, "den", d)

    @staticmethod
    def cast(x: Rat | F | int) -> Rat:
        return x if isinstance(x, Rat) else Rat(x)

    def __add__(self, other: Rat | F | int) -> Rat:
        y = self.cast(other)
        return Rat(padd(pmul(self.num, y.den), pmul(y.num, self.den)),
                   pmul(self.den, y.den))

    __radd__ = __add__

    def __neg__(self) -> Rat:
        return Rat(pneg(self.num), self.den)

    def __sub__(self, other: Rat | F | int) -> Rat:
        return self + (-self.cast(other))

    def __rsub__(self, other: Rat | F | int) -> Rat:
        return self.cast(other) - self

    def __mul__(self, other: Rat | F | int) -> Rat:
        y = self.cast(other)
        return Rat(pmul(self.num, y.num), pmul(self.den, y.den))

    __rmul__ = __mul__

    def __truediv__(self, other: Rat | F | int) -> Rat:
        y = self.cast(other)
        return Rat(pmul(self.num, y.den), pmul(self.den, y.num))

    def __rtruediv__(self, other: Rat | F | int) -> Rat:
        return self.cast(other) / self

    def __pow__(self, n: int) -> Rat:
        if not isinstance(n, int):
            raise TypeError("only ordinary integer powers are supported")
        if n < 0:
            return (Rat(1) / self) ** (-n)
        r, a = Rat(1), self
        while n:
            if n & 1:
                r = r * a
            a = a * a
            n //= 2
        return r

    def sign(self) -> int:
        if self.num == (F(0),):
            return 0
        c = self.num[order(self.num)] / self.den[order(self.den)]
        return 1 if c > 0 else -1

    def __abs__(self) -> Rat:
        return self if self.sign() >= 0 else -self

    def val(self) -> int | float:
        return math.inf if self.num == (F(0),) else order(self.num) - order(self.den)

    def leading(self) -> F:
        if not self.sign():
            raise ValueError("zero has no leading coefficient")
        return self.num[order(self.num)] / self.den[order(self.den)]

    def residue(self) -> F:
        if self.val() < 0:
            raise ValueError("standard part requested for an unlimited value")
        return self.leading() if self.val() == 0 else F(0)

    def coeff(self, exponent: int) -> F:
        if self.num == (F(0),):
            return F(0)
        on, od = order(self.num), order(self.den)
        k = exponent - (on - od)
        if k < 0:
            return F(0)
        n, d = self.num[on:], self.den[od:]
        c: list[F] = []
        for r in range(k + 1):
            v = n[r] if r < len(n) else F(0)
            for j in range(1, min(r, len(d) - 1) + 1):
                v -= d[j] * c[r - j]
            c.append(v / d[0])
        return c[k]


def eq(x: Rat | F | int, y: Rat | F | int) -> bool:
    return (Rat.cast(x) - y).sign() == 0


def ge(x: Rat | F | int, y: Rat | F | int = 0) -> bool:
    return (Rat.cast(x) - y).sign() >= 0


def normalize(weights: list[Rat]) -> list[Rat]:
    s = sum(weights, Rat())
    if s.sign() <= 0 or any(w.sign() < 0 for w in weights):
        raise ValueError("normalization requires nonnegative nonzero weights")
    return [w / s for w in weights]


def event(p: list[Rat], mask: int) -> Rat:
    return sum((x for i, x in enumerate(p) if (mask >> i) & 1), Rat())


def rank(rows: list[list[F]]) -> int:
    if not rows:
        return 0
    a = [row[:] for row in rows]
    r = 0
    for c in range(len(a[0])):
        piv = next((i for i in range(r, len(a)) if a[i][c]), None)
        if piv is None:
            continue
        a[r], a[piv] = a[piv], a[r]
        d = a[r][c]
        a[r] = [x / d for x in a[r]]
        for i in range(len(a)):
            if i != r:
                d = a[i][c]
                a[i] = [x - d * y for x, y in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


class Checks:
    def __init__(self) -> None:
        self.counts: Counter[str] = Counter()

    def check(self, family: str, condition: bool, detail: str = "") -> None:
        if not condition:
            raise AssertionError(f"{family}: {detail}")
        self.counts[family] += 1


def run() -> dict:
    rng = random.Random(1729)
    c = Checks()
    t = Rat((0, 1))
    one = Rat(1)
    c.check("arithmetic", eq((1 - t) * sum((t**j for j in range(9)), Rat()), 1-t**9))
    c.check("arithmetic", eq((t**3 + t**2) / (t + 1), t**2))
    c.check("arithmetic", ((t**-2).val(), (3*t**2).leading()) == (-2, F(3)))
    c.check("arithmetic", ge(1-1000000*t) and ge(t-t**2))

    for case in range(48):
        n = rng.randint(2, 5)
        weights = [rng.randint(1, 4) * t**rng.randint(0, 4) *
                   (1 + rng.randint(-2, 3)*t**rng.randint(1, 3)) for _ in range(n)]
        p = normalize(weights)
        likelihood = [F(rng.randint(1, 4), 5)*t**rng.randint(0, 4) for _ in range(n)]
        q = normalize([x*y for x, y in zip(p, likelihood)])
        c.check("bayes_normalization", eq(sum(q, Rat()), 1))
        c.check("bayes_normalization", all(x.sign() > 0 for x in q))
        m = min(x.val()+y.val() for x, y in zip(p, likelihood))
        d = sum(x.leading()*y.leading() for x, y in zip(p, likelihood)
                if x.val()+y.val() == m)
        for x, y, z in zip(p, likelihood, q):
            c.check("scale_bayes", z.val() == x.val()+y.val()-m)
            c.check("scale_bayes", z.leading() == x.leading()*y.leading()/d)
        l2 = [t**rng.randint(0, 3) for _ in range(n)]
        qa = normalize([x*y for x, y in zip(q, l2)])
        qb = normalize([x*y*z for x, y, z in zip(p, likelihood, l2)])
        c.check("update_order", all(eq(x, y) for x, y in zip(qa, qb)))
        c.check("odds_update", eq(q[0]/q[1], (p[0]/p[1])*(likelihood[0]/likelihood[1])))

        masks = list(range(1, 1 << n))
        rng.shuffle(masks)
        for b in masks[:5]:
            a = rng.randrange(1 << n)
            amin = min(p[i].val() for i in range(n) if (b >> i) & 1)
            den = sum(p[i].leading() for i in range(n)
                      if ((b >> i) & 1) and p[i].val() == amin)
            num = sum(p[i].leading() for i in range(n)
                      if ((a & b) >> i) & 1 and p[i].val() == amin)
            c.check("conditional_skeleton", (event(p, a & b)/event(p, b)).residue() == num/den)

        xs = [rng.randint(-3, 3) for _ in range(n)]
        ys = [rng.randint(-3, 3) for _ in range(n)]
        ex = sum((z*x for z, x in zip(p, xs)), Rat())
        ex2 = sum((z*x*x for z, x in zip(p, xs)), Rat())
        ey2 = sum((z*y*y for z, y in zip(p, ys)), Rat())
        exy = sum((z*x*y for z, x, y in zip(p, xs, ys)), Rat())
        variance = ex2-ex*ex
        c.check("finite_inequalities", ge(variance))
        c.check("finite_inequalities", ge(ex2*ey2-exy**2))
        tail = sum((z for z, x in zip(p, xs) if ge(abs(Rat(x)-ex), 1)), Rat())
        c.check("finite_inequalities", ge(variance, tail))
        xp = [x+3 for x in xs]
        xp_mean = sum((z*x for z, x in zip(p, xp)), Rat())
        markov_tail = sum((z for z, x in zip(p, xp) if x >= 2), Rat())
        c.check("finite_inequalities", ge(xp_mean/2, markov_tail))

    p = [1-2*t, t, t]
    q = [1-4*t, t, 3*t]
    c.check("rare_shadow", all(x.residue() == y.residue() for x, y in zip(p, q)))
    c.check("rare_shadow", eq(p[1]/(p[1]+p[2]), F(1, 2)))
    c.check("rare_shadow", eq(q[1]/(q[1]+q[2]), F(1, 4)))
    c.check("rare_shadow", eq(sum((abs(x-y) for x, y in zip(p, q)), Rat())/2, 2*t))
    for lam in range(8):
        h = t**(lam+2)
        q = [p[0]-h, p[1], p[2]+h]
        delta = sum((abs(x-y) for x, y in zip(p, q)), Rat())/2
        cb = p[1]/(p[1]+p[2]) - q[1]/(q[1]+q[2])
        c.check("conditional_precision", cb.val() > lam)
        c.check("conditional_precision", ge(2*delta/(p[1]+p[2]), abs(cb)))
        c.check("conditional_precision", eq(sum(q, Rat()), 1) and all(x.sign() > 0 for x in q))

    prior = normalize([one, t, t**2])
    post = normalize([prior[0]*t**3, prior[1]*t, prior[2]])
    c.check("worked_bayes", all(eq(x, y) for x, y in zip(post, [t/(2+t), 1/(2+t), 1/(2+t)])))
    u, v = t**2, (1+t)/t
    intersection = (u/(1+u))*(v/(1+v))
    c.check("logit_rational_identity", eq(intersection/(1-intersection), u*v/(1+u+v)))
    for k in range(1, 16):
        c.check("logistic_tail_coefficients", (t/(1+t)).coeff(k) == (-1)**(k-1))

    for model in range(6):
        n = 4
        rows = [[F(1, n)]*n]
        for j in range(1, 7):
            r = [F(rng.randint(-3, 3)) for _ in range(n-1)]
            rows.append(r+[-sum(r)])
        p = [Rat(tuple(rows[j][i] for j in range(len(rows)))) for i in range(n)]
        chosen: list[list[F]] = []
        for row in rows:
            if rank(chosen+[row]) > len(chosen):
                chosen.append(row)
        c.check("signed_compression", len(chosen) <= n and eq(sum(p, Rat()), 1))
        for j in range(40):
            d = [rng.randint(-4, 4) for _ in range(n)]
            actual = sum((x*y for x, y in zip(p, d)), Rat()).sign()
            pairings = [sum(x*y for x, y in zip(row, d)) for row in chosen]
            first = next((x for x in pairings if x), F(0))
            wanted = (first > 0)-(first < 0)
            c.check("signed_compression", actual == wanted)

    for n in range(1, 31):
        first_success = t*(1-t)**(n-1)
        c.check("rare_coin_coefficients", first_success.coeff(1) == 1)
        partial = sum(((1-t)*t**j for j in range(n)), Rat())
        c.check("strong_geometric_finite_identity", eq(partial, 1-t**n))
        e2 = e4 = eabs = F(0)
        variation = F(0)
        for k in range(n+1):
            prob = (F(1, 2)+t)**k * (F(1, 2)-t)**(n-k)
            row = prob.coeff(1)
            wanted = F(2*(2*k-n), 2**n)
            c.check("fair_coin_coefficients", row == wanted)
            mass = F(math.comb(n, k), 2**n)
            s = 2*k-n
            e2 += mass*s*s
            e4 += mass*s**4
            eabs += mass*abs(s)
            variation += math.comb(n, k)*abs(row)
        c.check("rademacher_moments", e2 == n)
        c.check("rademacher_moments", e4 == 3*n*n-2*n)
        c.check("rademacher_moments", eabs*eabs >= F(n, 3))
        c.check("rademacher_moments", variation == 2*eabs)

    mean = (F(1, 3)+F(2, 3)*t)/(1+t)
    cross = (F(1, 9)+F(4, 9)*t)/(1+t)
    c.check("latent_model", eq(cross-mean**2, t/(9*(1+t)**2)))
    for n in range(1, 9):
        prior1 = t/(1+t)
        posterior_expectation = Rat()
        for k in range(n+1):
            l0 = Rat(F(1, 3)**k * F(2, 3)**(n-k))
            l1 = Rat(F(2, 3)**k * F(1, 3)**(n-k))
            joint1 = t*l1/(1+t)
            path = (l0+t*l1)/(1+t)
            posterior = joint1/path
            bf = F(2)**(2*k-n)
            c.check("latent_model", eq(posterior, t*bf/(1+t*bf)))
            c.check("latent_model", posterior.residue() == 0)
            posterior_expectation += math.comb(n, k)*path*posterior
        c.check("latent_model", eq(posterior_expectation, prior1))

    for trial in range(20):
        counts = [rng.randint(0, 6) for _ in range(5)]
        if not sum(counts):
            counts[0] = 1
        a = [rng.randint(1, 4) for _ in counts]
        smoothed = normalize([Rat(n)+t*x for n, x in zip(counts, a)])
        c.check("smoothing", all(x.sign() > 0 for x in smoothed))
        c.check("smoothing", eq(sum(smoothed, Rat()), 1))
        for x, n in zip(smoothed, counts):
            c.check("smoothing", x.residue() == F(n, sum(counts)))

    return {
        "status": "PASS",
        "python": platform.python_version(),
        "arithmetic": "Exact fractions and normalized rational functions in Q(t)",
        "order": "t is positive infinitesimal; signs use leading coefficients",
        "seed": 1729,
        "assertions_passed": sum(c.counts.values()),
        "test_families": dict(sorted(c.counts.items())),
        "limitations": [
            "Finite examples, not formal proofs of the general theorems.",
            "No canonical surreal exponential or logarithm is implemented.",
            "No infinite summation, measure extension, saturation, or compactness is computed.",
            "No floating-point surrogate is used for t."
        ]
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Optional JSON result file")
    args = parser.parse_args()
    result = run()
    text = json.dumps(result, indent=2)
    print(text)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text+"\n", encoding="utf-8")


if __name__ == "__main__":
    main()
