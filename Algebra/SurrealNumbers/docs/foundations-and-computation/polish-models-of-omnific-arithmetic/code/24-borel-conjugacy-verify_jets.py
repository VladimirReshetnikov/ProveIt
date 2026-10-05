#!/usr/bin/env python3
"""Exact finite-jet regression checks for borel_conjugacy.tex.

Only the Python standard library is used.  All arithmetic is rational.
These checks test formulas on Q[z]/(z^(N+1)), z=t^(1/d); they are NOT
proofs about arbitrary left-finite supports or descriptive set theory.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
import json
from math import factorial
from pathlib import Path
import random
from typing import Iterable


@dataclass(frozen=True)
class Jet:
    """A rational truncated power series with fixed maximum degree."""
    a: tuple[F, ...]

    @classmethod
    def make(cls, n: int, values: Iterable[int | F] = ()) -> Jet:
        if n < 0:
            raise ValueError("degree must be nonnegative")
        vals = tuple(F(x) for x in values)
        return cls((vals + (F(0),) * (n + 1))[:n + 1])

    @property
    def n(self) -> int:
        return len(self.a) - 1

    def one(self) -> Jet:
        return Jet.make(self.n, [1])

    def zero(self) -> Jet:
        return Jet.make(self.n)

    def _compatible(self, other: Jet) -> None:
        if self.n != other.n:
            raise ValueError("different truncation degrees")

    def __add__(self, other: Jet) -> Jet:
        self._compatible(other)
        return Jet(tuple(x + y for x, y in zip(self.a, other.a)))

    def __sub__(self, other: Jet) -> Jet:
        return self + other.scale(-1)

    def scale(self, q: int | F) -> Jet:
        return Jet(tuple(F(q) * x for x in self.a))

    def __mul__(self, other: Jet) -> Jet:
        self._compatible(other)
        out = [F(0)] * (self.n + 1)
        for i, x in enumerate(self.a):
            if x:
                for j, y in enumerate(other.a[:self.n + 1 - i]):
                    if y:
                        out[i + j] += x * y
        return Jet(tuple(out))

    def shift(self, k: int) -> Jet:
        if k < 0:
            raise ValueError("only nonnegative shifts are implemented")
        return Jet.make(self.n, (F(0),) * min(k, self.n + 1) + self.a)

    def euler(self, d: int) -> Jet:
        if d < 1:
            raise ValueError("grid denominator must be positive")
        return Jet(tuple(x * F(i, d) for i, x in enumerate(self.a)))

    def power(self, beta: int | F) -> Jet:
        """Binomial power of a unit, using U V' = beta U' V."""
        if self.a[0] != 1:
            raise ValueError("power requires a unit with constant coefficient 1")
        b = F(beta)
        out = [F(1)] + [F(0)] * self.n
        for n in range(1, self.n + 1):
            out[n] = sum((((b + 1) * k - n) * self.a[k] * out[n-k]
                          for k in range(1, n+1)), F(0)) / n
        return Jet(tuple(out))

    def log(self) -> Jet:
        if self.a[0] != 1:
            raise ValueError("log requires a unit with constant coefficient 1")
        inv = self.power(-1)
        # Integrate U'/U in z, independently of the power recurrence.
        deriv = Jet.make(self.n, [i * self.a[i] for i in range(1, self.n + 1)])
        prod = deriv * inv
        return Jet.make(self.n, [0] + [prod.a[i-1] / i for i in range(1, self.n+1)])

    def exp(self) -> Jet:
        if self.a[0] != 0:
            raise ValueError("exp requires zero constant coefficient")
        out = [F(1)] + [F(0)] * self.n
        for n in range(1, self.n+1):
            out[n] = sum((k * self.a[k] * out[n-k]
                          for k in range(1, n+1)), F(0)) / n
        return Jet(tuple(out))

    def j(self, d: int) -> Jet:
        return Jet(tuple(F(0) if i == 0 else x * F(d, i)
                         for i, x in enumerate(self.a)))

    def is_zero(self) -> bool:
        return not any(self.a)

    def sparse(self) -> dict[str, str]:
        return {str(i): str(x) for i, x in enumerate(self.a) if x}


def normalizer(unit: Jet, alpha: F, c: F, d: int) -> tuple[Jet, F, int]:
    """Return H with h=tH, residue rho, and iteration count."""
    if unit.a[0] != 1 or not c:
        raise ValueError("invalid derivation parameters")
    aa = alpha * d
    if aa.denominator != 1:
        raise ValueError("alpha must be on the grid")
    A = int(aa)
    inv = unit.power(-1)
    if alpha == 0:
        return (inv - unit.one()).j(d).exp(), 1/c, 0
    rho = inv.a[A] / c if 0 < A <= unit.n else F(0)
    if A > unit.n:
        raise ValueError("residue lies above this test's truncation")
    vals = [F(1)]
    for j in range(1, unit.n+1):
        vals.append(F(0) if j == A else alpha * inv.a[j] / (alpha - F(j, d)))
    K = Jet(tuple(vals))
    if alpha < 0:
        return K.power(-1/alpha), rho, 0
    H = unit.one()
    # At least A additional correct z-coefficients per nontrivial iteration.
    for step in range(1, unit.n // A + 4):
        new = (K + H.log().shift(A).scale(alpha * c * rho)).power(-1/alpha)
        if new == H:
            return new, rho, step
        H = new
    raise AssertionError("finite-jet contraction did not stabilize")


def check_normalizer(unit: Jet, alpha: F, c: F, d: int) -> tuple[Jet, F, int]:
    H, rho, steps = normalizer(unit, alpha, c, d)
    denominator = unit.one()
    if alpha > 0:
        denominator += H.power(alpha).shift(int(alpha*d)).scale(c*rho)
    residual = unit * (H + H.euler(d)) * denominator - H.power(1+alpha)
    if not residual.is_zero():
        raise AssertionError(f"nonzero normalization residual: {residual.sparse()}")
    return H, rho, steps


def flow_unit(unit: Jet, alpha: F, c: F, d: int, s: F) -> Jet:
    """Compute exp(s D)(t)/t for positive-gain D=c t^alpha U E."""
    A = alpha*d
    if alpha <= 0 or A.denominator != 1:
        raise ValueError("flow test requires positive grid-aligned alpha")
    A = int(A)
    out = unit.zero()
    fn = unit.one()
    for n in range(unit.n // A + 1):
        out += fn.shift(n*A).scale((s*c)**n / factorial(n))
        fn = unit * (fn.scale(1+n*alpha) + fn.euler(d))
    return out


def compose_units(outer: Jet, inner: Jet, d: int) -> Jet:
    """Return g_outer(g_inner(t))/t for g=t times its unit."""
    result = outer.zero()
    for j, q in enumerate(outer.a):
        if q:
            result += inner.power(F(j, d)).shift(j).scale(q)
    return inner * result


def random_unit(rng: random.Random, n: int, max_degree: int = 5) -> Jet:
    vals = [F(1)] + [F(rng.randint(-2, 2), rng.randint(1, 3))
                    for _ in range(min(n, max_degree))]
    return Jet.make(n, vals)


def run(degree: int, seed: int, random_cases: int) -> dict:
    if degree < 12:
        raise ValueError("use a truncation degree of at least 12")
    if random_cases < 0:
        raise ValueError("random case count must be nonnegative")
    rng = random.Random(seed)
    counts = {"normalization": 0, "residue_covariance": 0,
              "positive_flow_group_law": 0, "positive_flow_inverse": 0,
              "exp_log": 0, "zero_gain_closed_flow": 0}
    max_steps = 0
    # Explicit positive-, zero-, and negative-gain examples from the paper.
    examples = []
    specs = [(6, F(1,2), F(2), [1,1], "positive_hidden_residue"),
             (2, F(0), F(3), [1,1], "zero_gain"),
             (2, F(-1), F(1), [1,1], "negative_gain")]
    for d, alpha, c, vals, name in specs:
        U = Jet.make(degree, vals)
        H, rho, steps = check_normalizer(U, alpha, c, d)
        counts["normalization"] += 1
        max_steps = max(max_steps, steps)
        examples.append({"name": name, "d": d, "alpha": str(alpha), "c": str(c),
                         "rho": str(rho), "h_over_t_coefficients": H.sparse()})
    for k in range(random_cases):
        d = rng.choice([1,2,3,6])
        alpha = F(rng.choice([-5,-3,-1,0,1,2,3,5]), d)
        c = F(rng.choice([-3,-2,-1,1,2,3]), rng.choice([1,2]))
        U = random_unit(rng, degree)
        _, _, steps = check_normalizer(U, alpha, c, d)
        counts["normalization"] += 1
        max_steps = max(max_steps, steps)
        V = random_unit(rng, degree)
        if V.log().exp() != V:
            raise AssertionError("exp(log(V)) failure")
        counts["exp_log"] += 1
    # Pull back a normal vector field under h=t^r H and re-extract its residue.
    for k in range(max(6, random_cases // 2)):
        d = 6
        alpha_b = F(rng.choice([1,2,3]),6)
        r = F(rng.choice([1,2,3]))
        alpha_a = r * alpha_b
        cb = F(rng.choice([-2,-1,1,2]))
        rhob = F(rng.randint(-3,3), rng.choice([1,2,3]))
        ca = cb/r
        H = random_unit(rng, degree, 3)
        denominator = H.one() + H.power(alpha_b).shift(int(alpha_a*d)).scale(cb*rhob)
        logarithmic_derivative = H.one() + H.log().euler(d).scale(1/r)
        Ua = H.power(alpha_b) * denominator.power(-1) * logarithmic_derivative.power(-1)
        rhoa = Ua.power(-1).a[int(alpha_a*d)] / ca
        if rhoa != r*rhob:
            raise AssertionError("residue covariance failure")
        counts["residue_covariance"] += 1
    for k in range(max(4, random_cases // 6)):
        d = 2
        alpha = F(rng.choice([1,2,3]),2)
        c = F(rng.choice([-2,-1,1,2]))
        U = random_unit(rng, degree, 3)
        s, r = F(1,2), F(-2,3)
        gs, gr = flow_unit(U,alpha,c,d,s), flow_unit(U,alpha,c,d,r)
        if compose_units(gs, gr, d) != flow_unit(U,alpha,c,d,s+r):
            raise AssertionError("positive-flow group law failure")
        counts["positive_flow_group_law"] += 1
        if compose_units(gs, flow_unit(U,alpha,c,d,-s),d) != U.one():
            raise AssertionError("positive-flow inverse failure")
        counts["positive_flow_inverse"] += 1
    # Zero-gain example: put B=exp(3s/2); g_s/t=B^2(1+(1-B)z)^(-2).
    # Check h(g_s)=exp(3s)h using rational B, without floating-point exp.
    zunit = Jet.make(degree,[1,1])
    hunit = zunit.power(-2)
    for B in [F(1,2), F(2), F(3,2), F(1)]:
        C = Jet.make(degree,[1,1-B])
        Gunit = C.power(-2)  # g/t = B^2 Gunit, sqrt(g)=B z/C
        inside_h_unit = Gunit * (Gunit.one() + C.power(-1).shift(1).scale(B)).power(-2)
        if inside_h_unit != hunit:
            raise AssertionError("zero-gain closed-flow conjugacy failure")
        counts["zero_gain_closed_flow"] += 1
    return {"status":"PASS", "arithmetic":"fractions.Fraction (exact rational)",
            "truncation":"Q[z]/(z^(N+1)); z=t^(1/d)", "N":degree,
            "seed":seed, "random_cases":random_cases, "checks":counts,
            "total_checks":sum(counts.values()), "maximum_fixed_point_steps":max_steps,
            "examples":examples,
            "limitations":["Finite jets only; no test of arbitrary unbounded-denominator supports.",
                           "Not a proof of Borel uniformity, smoothness, or the flow obstruction.",
                           "Not a Lean or Rocq formalization."]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--degree", type=int, default=24)
    parser.add_argument("--seed", type=int, default=20261004)
    parser.add_argument("--random-cases", type=int, default=48)
    parser.add_argument("--output", type=Path, default=Path("verification_report.json"))
    args = parser.parse_args()
    report = run(args.degree, args.seed, args.random_cases)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key,value in report.items() if key != "examples"}, indent=2))


if __name__ == "__main__":
    main()
