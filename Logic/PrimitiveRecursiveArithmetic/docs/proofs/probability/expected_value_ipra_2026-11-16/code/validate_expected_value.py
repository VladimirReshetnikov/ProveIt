#!/usr/bin/env python3
"""Exact regression checks for the expected-value iPRA packet.

All arithmetic uses fractions.Fraction.  The checks are finite diagnostics,
not a substitute for an iPRA or Lean proof.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Callable, Iterable, Sequence

Q = Fraction


@dataclass(frozen=True)
class FiniteLaw:
    weights: tuple[int, ...]

    def __post_init__(self) -> None:
        if not self.weights or any(w < 0 for w in self.weights):
            raise ValueError("weights must be a nonempty tuple of naturals")
        if self.total <= 0:
            raise ValueError("total weight must be positive")

    @property
    def total(self) -> int:
        return sum(self.weights)

    @property
    def n(self) -> int:
        return len(self.weights)

    def expect(self, values: Sequence[Q]) -> Q:
        if len(values) != self.n:
            raise ValueError("value length mismatch")
        return sum((Q(w) * Q(x) for w, x in zip(self.weights, values)), Q(0)) / self.total

    def prob(self, predicate: Sequence[bool]) -> Q:
        if len(predicate) != self.n:
            raise ValueError("predicate length mismatch")
        return Q(sum(w for w, hit in zip(self.weights, predicate) if hit), self.total)


def mean(law: FiniteLaw, x: Sequence[Q]) -> Q:
    return law.expect(x)


def variance(law: FiniteLaw, x: Sequence[Q]) -> Q:
    mu = mean(law, x)
    return law.expect([(Q(v) - mu) ** 2 for v in x])


def second_moment(law: FiniteLaw, x: Sequence[Q]) -> Q:
    return law.expect([Q(v) ** 2 for v in x])


def tail_sum(law: FiniteLaw, x: Sequence[int]) -> Q:
    if any(v < 0 for v in x):
        raise ValueError("tail_sum expects nonnegative integers")
    bound = max(x, default=0)
    return sum((law.prob([v > k for v in x]) for k in range(bound)), Q(0))


def product_law(a: FiniteLaw, b: FiniteLaw) -> FiniteLaw:
    return FiniteLaw(tuple(wa * wb for wa in a.weights for wb in b.weights))


def product_values(x: Sequence[Q], y: Sequence[Q], op: Callable[[Q, Q], Q]) -> list[Q]:
    return [op(Q(xi), Q(yj)) for xi in x for yj in y]


def falling(x: int, r: int) -> int:
    out = 1
    for j in range(r):
        out *= x - j
    return out


class Recorder:
    def __init__(self) -> None:
        self.assertions = 0
        self.groups: list[dict[str, object]] = []

    def check(self, condition: bool, message: str = "") -> None:
        self.assertions += 1
        if not condition:
            raise AssertionError(message or "exact validation failed")

    def group(self, name: str, before: int, note: str = "") -> None:
        self.groups.append(
            {
                "name": name,
                "assertions": self.assertions - before,
                "note": note,
            }
        )


def run_validation() -> dict[str, object]:
    r = Recorder()

    # 1. Article examples.
    before = r.assertions
    die = FiniteLaw((1, 1, 1, 1, 1, 1))
    die_x = [Q(i) for i in range(1, 7)]
    r.check(die.expect(die_x) == Q(7, 2), "die mean")
    roulette = FiniteLaw((37, 1))
    r.check(roulette.expect([Q(-1), Q(35)]) == Q(-1, 19), "roulette mean")
    r.check(Q(190) * roulette.expect([Q(-1), Q(35)]) == Q(-10), "190 roulette bets")
    r.group("article examples", before)

    # 2. Exhaustive elementary laws.
    before = r.assertions
    laws: list[FiniteLaw] = []
    for n in (1, 2, 3):
        for ws in itertools.product(range(3), repeat=n):
            if sum(ws) > 0:
                laws.append(FiniteLaw(tuple(ws)))
    value_sets = list(itertools.product(range(-2, 3), repeat=3))
    for law in laws:
        vals_pool = value_sets if law.n == 3 else itertools.product(range(-2, 3), repeat=law.n)
        for raw in vals_pool:
            x = [Q(v) for v in raw]
            mu = law.expect(x)
            r.check(law.expect([Q(1)] * law.n) == 1, "normalization")
            r.check(law.expect([Q(5, 3)] * law.n) == Q(5, 3), "constant")
            r.check(min(x) <= mu <= max(x), "convex hull")
            r.check(abs(mu) <= law.expect([abs(v) for v in x]), "absolute expectation")
            r.check(variance(law, x) == second_moment(law, x) - mu * mu, "variance identity")
            r.check(law.expect([max(v, 0) - max(-v, 0) for v in x]) == mu, "positive/negative parts")
            r.check(law.expect([Q(1) if v == 0 else Q(0) for v in x]) == law.prob([v == 0 for v in x]), "indicator")
    r.group("finite normalization, bounds, parts, indicators, variance", before)

    # 3. Linearity and monotonicity on a representative exhaustive family.
    before = r.assertions
    for law in laws:
        candidates = list(itertools.product(range(-2, 3), repeat=law.n))
        stride = max(1, len(candidates) // 20)
        sampled = candidates[::stride]
        for xr in sampled:
            x = [Q(v) for v in xr]
            for yr in sampled:
                y = [Q(v) for v in yr]
                a = Q(3, 2)
                r.check(
                    law.expect([x[i] + y[i] for i in range(law.n)]) == law.expect(x) + law.expect(y),
                    "additivity",
                )
                r.check(law.expect([a * v for v in x]) == a * law.expect(x), "homogeneity")
                if all(xi <= yi for xi, yi in zip(x, y)):
                    r.check(law.expect(x) <= law.expect(y), "monotonicity")
    r.group("linearity and monotonicity", before)

    # 4. Finite tail sum and signed tail identity.
    before = r.assertions
    for law in laws:
        for raw in itertools.product(range(5), repeat=law.n):
            x = list(raw)
            r.check(law.expect([Q(v) for v in x]) == tail_sum(law, x), "nonnegative tail sum")
        for raw in itertools.product(range(-3, 4), repeat=law.n):
            x = list(raw)
            pos = sum((law.prob([v > k for v in x]) for k in range(0, 3)), Q(0))
            neg = sum((law.prob([v <= -k - 1 for v in x]) for k in range(0, 3)), Q(0))
            r.check(law.expect([Q(v) for v in x]) == pos - neg, "signed integer tail formula")
    r.group("tail formulas", before)

    # 5. Markov and Chebyshev.
    before = r.assertions
    thresholds = [Q(1, 2), Q(1), Q(3, 2), Q(2), Q(3)]
    nonnegative_values = list(itertools.product(range(5), repeat=3))
    for law in [L for L in laws if L.n == 3]:
        for raw in nonnegative_values[::7]:
            x = [Q(v) for v in raw]
            ex = law.expect(x)
            for a in thresholds:
                r.check(law.prob([v >= a for v in x]) <= ex / a, "Markov")
        for raw in value_sets[::7]:
            x = [Q(v) for v in raw]
            mu = law.expect(x)
            var = variance(law, x)
            for a in [Q(1), Q(2), Q(5, 2)]:
                r.check(law.prob([abs(v - mu) >= a for v in x]) <= var / (a * a), "Chebyshev")
    die_var = variance(die, die_x)
    r.check(die_var == Q(35, 12), "die variance")
    r.check(1 - die_var / Q(5, 2) ** 2 == Q(8, 15), "Wikipedia 53 percent arithmetic")
    r.check(die.prob([Q(1) < v < Q(6) for v in die_x]) == Q(2, 3), "open die interval actual")
    r.check(die.prob([Q(1) <= v <= Q(6) for v in die_x]) == 1, "inclusive die interval actual")
    r.group("Markov, Chebyshev, and die audit", before)

    # 6. Cauchy-Schwarz and exact Lagrange identity.
    before = r.assertions
    for law in [FiniteLaw((1, 1)), FiniteLaw((1, 2, 3)), FiniteLaw((2, 0, 1))]:
        for ur in itertools.product(range(-2, 3), repeat=law.n):
            u = [Q(v) for v in ur]
            for vr in itertools.product(range(-2, 3), repeat=law.n):
                v = [Q(x) for x in vr]
                lhs = law.expect([u[i] * v[i] for i in range(law.n)]) ** 2
                rhs = law.expect([z * z for z in u]) * law.expect([z * z for z in v])
                r.check(lhs <= rhs, "Cauchy-Schwarz")
                A = sum((Q(w) * u[i] ** 2 for i, w in enumerate(law.weights)), Q(0))
                B = sum((Q(w) * v[i] ** 2 for i, w in enumerate(law.weights)), Q(0))
                C = sum((Q(w) * u[i] * v[i] for i, w in enumerate(law.weights)), Q(0))
                lagrange = sum(
                    (
                        Q(law.weights[i] * law.weights[j])
                        * (u[i] * v[j] - u[j] * v[i]) ** 2
                        for i in range(law.n)
                        for j in range(i + 1, law.n)
                    ),
                    Q(0),
                )
                r.check(A * B - C * C == lagrange, "weighted Lagrange identity")
    r.group("Cauchy-Schwarz and Lagrange identity", before)

    # 7. Product laws and multiplicativity under independence.
    before = r.assertions
    product_examples = [
        (FiniteLaw((1, 1)), [Q(-1), Q(1)], FiniteLaw((1, 2)), [Q(0), Q(3)]),
        (FiniteLaw((2, 3, 1)), [Q(-2), Q(0), Q(5)], FiniteLaw((4, 1)), [Q(2), Q(-1)]),
    ]
    for la, x, lb, y in product_examples:
        lp = product_law(la, lb)
        xy = product_values(x, y, lambda a, b: a * b)
        r.check(lp.expect(xy) == la.expect(x) * lb.expect(y), "independent product expectation")
        r.check(lp.expect(product_values(x, y, lambda a, b: a + b)) == la.expect(x) + lb.expect(y), "product sum")
    symmetric = FiniteLaw((1, 1))
    x = [Q(-1), Q(1)]
    r.check(symmetric.expect([v * v for v in x]) == 1)
    r.check(symmetric.expect(x) * symmetric.expect(x) == 0)
    dep = FiniteLaw((1, 1, 1))
    depx = [Q(-1), Q(0), Q(1)]
    depy = [v * v for v in depx]
    r.check(dep.expect([depx[i] * depy[i] for i in range(3)]) == dep.expect(depx) * dep.expect(depy))
    r.group("independence, nonmultiplicativity, dependent equality", before)

    # 8. Conditional expectation / total expectation on finite partitions.
    before = r.assertions
    law = FiniteLaw((1, 2, 3, 4, 1))
    x = [Q(-2), Q(1), Q(5), Q(0), Q(7)]
    cell = [0, 0, 1, 1, 2]
    conditional: list[Q] = [Q(0)] * law.n
    for c in sorted(set(cell)):
        idx = [i for i, cc in enumerate(cell) if cc == c]
        mass = sum(law.weights[i] for i in idx)
        val = sum((Q(law.weights[i]) * x[i] for i in idx), Q(0)) / mass
        for i in idx:
            conditional[i] = val
    r.check(law.expect(conditional) == law.expect(x), "law of total expectation")
    r.group("finite conditional expectation", before)

    # 9. Binomial mean, sample mean, sample variance, and residual minimizer.
    before = r.assertions
    p = Q(2, 5)
    for n in range(1, 8):
        outcomes = list(itertools.product((0, 1), repeat=n))
        denom = 5**n
        weights = []
        sums = []
        avgs = []
        for outcome in outcomes:
            k = sum(outcome)
            weights.append(2**k * 3 ** (n - k))
            sums.append(Q(k))
            avgs.append(Q(k, n))
        law_n = FiniteLaw(tuple(weights))
        r.check(law_n.total == denom, "binomial normalization")
        r.check(law_n.expect(sums) == n * p, "binomial mean")
        r.check(law_n.expect(avgs) == p, "sample mean unbiased")
        r.check(variance(law_n, avgs) == p * (1 - p) / n, "sample mean variance")
    data = [Q(-2), Q(1), Q(3), Q(8)]
    xbar = sum(data, Q(0)) / len(data)
    base = sum(((z - xbar) ** 2 for z in data), Q(0))
    for a in [Q(-5), Q(0), Q(5, 2), Q(10)]:
        lhs = sum(((z - a) ** 2 for z in data), Q(0))
        rhs = base + len(data) * (a - xbar) ** 2
        r.check(lhs == rhs, "least-squares identity")
        r.check(lhs >= base, "sample mean minimizes residuals")
    r.group("binomial and sample-mean formulas", before)

    # 10. Geometric and Poisson finite identities.
    before = r.assertions
    for p in [Q(1, 2), Q(1, 3), Q(2, 5)]:
        q = 1 - p
        for N in range(1, 12):
            lhs = sum((Q(i) * p * q ** (i - 1) for i in range(1, N + 1)), Q(0))
            rhs = (1 - (N + 1) * q**N + N * q ** (N + 1)) / p
            tail = q**N * (N + 1 - N * q) / p
            r.check(lhs == rhs, "finite geometric first moment")
            r.check(lhs + tail == 1 / p, "geometric tail identity")
    for lam in [Q(1, 2), Q(1), Q(3, 2), Q(3)]:
        for N in range(1, 12):
            lhs = sum((Q(i) * lam**i / math.factorial(i) for i in range(N + 1)), Q(0))
            rhs = lam * sum((lam**j / math.factorial(j) for j in range(N)), Q(0))
            r.check(lhs == rhs, "Poisson shift identity before exp normalization")
    r.group("geometric and Poisson series identities", before)

    # 11. St Petersburg and rearranged alternating harmonic blocks.
    before = r.assertions
    for N in range(1, 30):
        stp = sum((Q(2**i) * Q(1, 2**i) for i in range(1, N + 1)), Q(0))
        r.check(stp == N, "St Petersburg partial expectation")
        alt = sum((Q(1 if k % 2 == 1 else -1, k) for k in range(1, 2 * N + 1)), Q(0))
        block = sum((Q(1, 4 * k - 3) + Q(1, 4 * k - 1) - Q(1, 2 * k) for k in range(1, N + 1)), Q(0))
        harmonic = lambda m: sum((Q(1, j) for j in range(1, m + 1)), Q(0))
        r.check(alt == harmonic(2 * N) - harmonic(N), "alternating harmonic finite identity")
        r.check(block == harmonic(4 * N) - Q(1, 2) * harmonic(2 * N) - Q(1, 2) * harmonic(N), "rearranged block identity")
    r.group("divergent and rearranged series diagnostics", before)

    # 12. Pointwise-to-zero spike and signed sigma-additivity counterexample.
    before = r.assertions
    for n in range(12):
        # On omega=0..N with dyadic mass 2^(-omega-1), plus a tail atom.
        N = 20
        weights = tuple(2 ** (N - k) for k in range(N + 1)) + (1,)
        law_d = FiniteLaw(weights)
        # total is 2^(N+1); last atom is the remaining tail 2^(-N-1).
        vals = [Q(0)] * (N + 2)
        vals[n] = Q(2 ** (n + 1))
        r.check(law_d.expect(vals) == 1, "dyadic spike expectation")
    # Finite partial telescoping: sum_{j=0}^N Y_j = X_N and each E[Y_j]
    # is 1 for j=0, 0 afterward.
    for N in range(1, 10):
        expectations = [Q(1)] + [Q(0)] * N
        r.check(sum(expectations, Q(0)) == 1, "telescoping expectation partial sum")
    r.group("pointwise/expectation and sigma-additivity counterexamples", before)

    # 13. Moment determinacy on bounded integer support via falling moments.
    before = r.assertions
    for B in range(0, 7):
        # The matrix is upper triangular in descending support order with
        # diagonal k!, so back-substitution is unique.
        matrix = [[falling(k, r_) if k >= r_ else 0 for k in range(B + 1)] for r_ in range(B + 1)]
        for k in range(B + 1):
            r.check(matrix[k][k] == math.factorial(k), "falling-moment diagonal")
        # Check reconstruction on several integer weight vectors.
        for weights in itertools.product(range(3), repeat=B + 1):
            if sum(weights) == 0:
                continue
            moments = [sum(weights[k] * matrix[r_][k] for k in range(B + 1)) for r_ in range(B + 1)]
            recovered = [Q(0)] * (B + 1)
            for k in range(B, -1, -1):
                residual = Q(moments[k]) - sum((Q(matrix[k][j]) * recovered[j] for j in range(k + 1, B + 1)), Q(0))
                recovered[k] = residual / math.factorial(k)
            r.check(recovered == [Q(w) for w in weights], "falling moments reconstruct masses")
    r.group("finite moment determinacy", before)

    # 14. Center of mass.
    before = r.assertions
    for law in [FiniteLaw((1, 1, 1)), FiniteLaw((2, 5, 3, 1))]:
        for raw in itertools.product(range(-3, 4), repeat=law.n):
            x = [Q(v) for v in raw]
            mu = law.expect(x)
            balance = sum((Q(w) * (x[i] - mu) for i, w in enumerate(law.weights)), Q(0))
            r.check(balance == 0, "center-of-mass balance")
    r.group("center of mass", before)

    # 15. Kolmogorov maximal inequality for small independent symmetric signs.
    before = r.assertions
    for n in range(1, 9):
        outcomes = list(itertools.product((-1, 1), repeat=n))
        law_s = FiniteLaw(tuple(1 for _ in outcomes))
        final = [Q(sum(o)) for o in outcomes]
        var_final = variance(law_s, final)
        r.check(var_final == n, "symmetric walk variance")
        for a in range(1, n + 1):
            hit = []
            for o in outcomes:
                s = 0
                maximum = 0
                for step in o:
                    s += step
                    maximum = max(maximum, abs(s))
                hit.append(maximum >= a)
            r.check(law_s.prob(hit) <= var_final / (a * a), "Kolmogorov maximal inequality")
    r.group("Kolmogorov maximal inequality", before)

    return {
        "status": "pass",
        "arithmetic": "fractions.Fraction only",
        "assertions": r.assertions,
        "groups": r.groups,
        "notes": [
            "These checks are regression evidence, not formal proofs.",
            "No floating-point value is used in a pass/fail assertion.",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=None)
    args = parser.parse_args()
    result = run_validation()
    text = json.dumps(result, indent=2, sort_keys=True)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text + "\n", encoding="utf-8")
    print(text)


if __name__ == "__main__":
    main()
