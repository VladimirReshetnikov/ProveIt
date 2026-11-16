#!/usr/bin/env python3
"""Exact finite-law reference implementation for the constructive CLT packet.

All algebraic assertions use fractions.Fraction.  Floating point is used only
for diagnostic evaluations of the Gaussian CDF and displayed local-limit
errors; it is never used as a proof oracle.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import erf, exp, factorial, log, pi, sqrt
from typing import Dict, Iterable, List, Mapping, Tuple
import argparse
import json


Q = Fraction


@dataclass(frozen=True)
class FiniteLaw:
    """A finite rational probability law, represented by exact masses."""

    mass: Mapping[Fraction, Fraction]

    def __post_init__(self) -> None:
        cleaned: Dict[Fraction, Fraction] = {}
        for x, p in self.mass.items():
            xq, pq = Q(x), Q(p)
            if pq < 0:
                raise ValueError("negative mass")
            if pq:
                cleaned[xq] = cleaned.get(xq, Q(0)) + pq
        if not cleaned:
            raise ValueError("empty law")
        if sum(cleaned.values(), Q(0)) != 1:
            raise ValueError("masses do not sum to one")
        object.__setattr__(self, "mass", dict(sorted(cleaned.items())))

    @staticmethod
    def from_weighted(values: Iterable[Tuple[Fraction, int]]) -> "FiniteLaw":
        vals = list(values)
        total = sum(w for _, w in vals)
        if total <= 0:
            raise ValueError("total weight must be positive")
        accumulated: Dict[Fraction, int] = {}
        for x, w in vals:
            if w < 0:
                raise ValueError("weights must be nonnegative")
            if w:
                qx = Q(x)
                accumulated[qx] = accumulated.get(qx, 0) + w
        return FiniteLaw({x: Q(w, total) for x, w in accumulated.items()})

    def expectation(self, f=lambda x: x) -> Fraction:
        return sum((p * Q(f(x)) for x, p in self.mass.items()), Q(0))

    @property
    def mean(self) -> Fraction:
        return self.expectation()

    @property
    def variance(self) -> Fraction:
        mu = self.mean
        return self.expectation(lambda x: (x - mu) ** 2)

    def centered_abs_moment(self, order: int) -> Fraction:
        if order < 0:
            raise ValueError("order must be nonnegative")
        mu = self.mean
        return self.expectation(lambda x: abs(x - mu) ** order)

    @property
    def radius(self) -> Fraction:
        mu = self.mean
        return max(abs(x - mu) for x in self.mass)

    def cdf(self, q: Fraction) -> Fraction:
        q = Q(q)
        return sum((p for x, p in self.mass.items() if x <= q), Q(0))

    def convolve(self, other: "FiniteLaw") -> "FiniteLaw":
        out: Dict[Fraction, Fraction] = {}
        for x, px in self.mass.items():
            for y, py in other.mass.items():
                out[x + y] = out.get(x + y, Q(0)) + px * py
        return FiniteLaw(out)

    def affine(self, a: Fraction, b: Fraction = Q(0)) -> "FiniteLaw":
        a, b = Q(a), Q(b)
        out: Dict[Fraction, Fraction] = {}
        for x, p in self.mass.items():
            y = a * x + b
            out[y] = out.get(y, Q(0)) + p
        return FiniteLaw(out)

    def iid_sum(self, n: int) -> "FiniteLaw":
        if n < 0:
            raise ValueError("n must be nonnegative")
        out = FiniteLaw({Q(0): Q(1)})
        base = self
        # Binary exponentiation under convolution keeps the implementation small.
        while n:
            if n & 1:
                out = out.convolve(base)
            n >>= 1
            if n:
                base = base.convolve(base)
        return out


def phi(x: float) -> float:
    return exp(-0.5 * x * x) / sqrt(2.0 * pi)


def Phi(x: float) -> float:
    return 0.5 * (1.0 + erf(x / sqrt(2.0)))


def kolmogorov_standardized(sum_law: FiniteLaw, raw_mean: Fraction, raw_var: Fraction) -> float:
    """Diagnostic d_K to N(0,1), checking both sides of every jump."""
    if raw_var <= 0:
        raise ValueError("positive variance required")
    sd = sqrt(float(raw_var))
    running = Q(0)
    best = 0.0
    for x, p in sum_law.mass.items():
        z = (float(x) - float(raw_mean)) / sd
        best = max(best, abs(float(running) - Phi(z)))
        running += p
        best = max(best, abs(float(running) - Phi(z)))
    return best


def berry_esseen_bound(base: FiniteLaw, n: int) -> float:
    var = float(base.variance)
    rho = float(base.centered_abs_moment(3))
    return min(1.0, 64.0 * rho / (var ** 1.5 * sqrt(n)))


def bounded_bound(base: FiniteLaw, n: int) -> float:
    var = float(base.variance)
    rad = float(base.radius)
    return min(1.0, 7.0 * rad / (sqrt(var) * sqrt(n)))


def binomial_law(n: int, p: Fraction) -> FiniteLaw:
    p = Q(p)
    q = 1 - p
    masses: Dict[Fraction, Fraction] = {}
    choose = 1
    for k in range(n + 1):
        if k > 0:
            choose = choose * (n - k + 1) // k
        masses[Q(k)] = Q(choose) * p**k * q ** (n - k)
    return FiniteLaw(masses)


def binomial_local_diagnostic(n: int, p: Fraction, k: int) -> dict:
    law = binomial_law(n, p)
    exact = float(law.mass[Q(k)])
    pf = float(p)
    qf = 1.0 - pf
    gauss = exp(-((k - n * pf) ** 2) / (2.0 * n * pf * qf)) / sqrt(2.0 * pi * n * pf * qf)
    theta = k / n
    m = min(pf, qf)
    A = abs(k - n * pf) / sqrt(n)
    if theta in (0.0, 1.0) or abs(theta - pf) > m / 2:
        log_bound = None
    else:
        log_bound = (
            2.0 * A / (m * sqrt(n))
            + 4.0 * A**3 / (3.0 * m**2 * sqrt(n))
            + (1.0 / 12.0 + 1.0 / (3.0 * m)) / n
        )
    return {
        "n": n,
        "p": str(p),
        "k": k,
        "exact": exact,
        "gaussian_local": gauss,
        "relative_error": abs(exact / gauss - 1.0),
        "proved_log_ratio_bound": log_bound,
        "derived_relative_bound_if_log_le_1": None if log_bound is None else 2.0 * log_bound,
    }


def pairwise_independent_row(m: int) -> dict:
    """The F_2^m character construction used in the manuscript counterexample."""
    if m < 1:
        raise ValueError
    n = 2**m - 1
    # For U=0 all characters are +1; for U!=0, orthogonality gives sum=-1.
    law = FiniteLaw({Q(n): Q(1, n + 1), Q(-1): Q(n, n + 1)})
    assert law.mean == 0
    assert law.variance == n
    return {
        "m": m,
        "n": n,
        "sum_law": {str(x): str(p) for x, p in law.mass.items()},
        "normalized_mass_near_zero": float(Q(n, n + 1)),
        "variance": str(law.variance),
    }


def lindeberg_not_lyapunov_row(m: int) -> dict:
    """Exact moments for the row in the Lyapunov non-converse example."""
    if m < 2:
        raise ValueError
    small_count = m * m - m
    small_var_each = Q(1, m * m)
    spike_variance = Q(1, m)
    total_var = small_count * small_var_each + spike_variance
    small_third = small_count * Q(1, m**3)
    spike_third = Q(m)  # p=m^-5, amplitude=m^2
    assert total_var == 1
    return {
        "m": m,
        "small_count": small_count,
        "total_variance": str(total_var),
        "lindeberg_tail_second_moment_for_fixed_epsilon_eventually": str(spike_variance),
        "third_moment_sum": str(small_third + spike_third),
    }


def exact_constant_checks() -> dict:
    # Rational consequences of 25/8 < pi < 16/5 and M<2/5.
    bounded_smoothing = Q(768, 125)
    bounded_integral = Q(11, 20)
    bounded_total = bounded_smoothing + bounded_integral
    be_smoothing = Q(6144, 125)
    be_integral = Q(8, 5)
    be_total = be_smoothing + be_integral
    assert bounded_total == Q(3347, 500)
    assert bounded_total < 7
    assert be_total == Q(6344, 125)
    assert be_total < 64
    return {
        "bounded_smoothing_upper": str(bounded_smoothing),
        "bounded_integral_upper": str(bounded_integral),
        "bounded_total_upper": str(bounded_total),
        "bounded_constant": 7,
        "berry_esseen_smoothing_upper": str(be_smoothing),
        "berry_esseen_integral_upper": str(be_integral),
        "berry_esseen_total_upper": str(be_total),
        "berry_esseen_constant": 64,
    }


def run_validation() -> dict:
    exact_assertions = 0
    diagnostic_checks = 0
    laws = {
        "bernoulli_1_3": FiniteLaw({Q(0): Q(2, 3), Q(1): Q(1, 3)}),
        "fair_die": FiniteLaw.from_weighted((Q(i), 1) for i in range(1, 7)),
        "skew_three_point": FiniteLaw({Q(-2): Q(1, 10), Q(0): Q(3, 5), Q(1): Q(3, 10)}),
    }
    diagnostics: List[dict] = []

    for name, law in laws.items():
        assert sum(law.mass.values(), Q(0)) == 1
        exact_assertions += 1
        assert law.variance > 0
        exact_assertions += 1
        for n in (1, 2, 5, 10, 25, 50):
            s = law.iid_sum(n)
            assert s.mean == n * law.mean
            exact_assertions += 1
            assert s.variance == n * law.variance
            exact_assertions += 1
            d = kolmogorov_standardized(s, n * law.mean, n * law.variance)
            be = berry_esseen_bound(law, n)
            bb = bounded_bound(law, n)
            # The theorem constants are deliberately coarse; every diagnostic
            # should lie below both displayed upper bounds.
            assert d <= be + 1e-14
            diagnostic_checks += 1
            assert d <= bb + 1e-14
            diagnostic_checks += 1
            diagnostics.append(
                {
                    "law": name,
                    "n": n,
                    "support_size": len(s.mass),
                    "actual_kolmogorov": d,
                    "berry_esseen_64_bound": be,
                    "bounded_7b_bound": bb,
                }
            )

    # Convolution algebra on two different laws.
    a, b = laws["bernoulli_1_3"], laws["skew_three_point"]
    c = a.convolve(b)
    assert c.mean == a.mean + b.mean
    exact_assertions += 1
    assert c.variance == a.variance + b.variance
    exact_assertions += 1

    # Exact finite Lyapunov -> Lindeberg inequality checks on arbitrary rows.
    for law in laws.values():
        mu = law.mean
        for eta in (Q(1, 4), Q(1, 2), Q(1), Q(2)):
            tail2 = law.expectation(lambda x: (x - mu) ** 2 if abs(x - mu) > eta else Q(0))
            tail3 = law.expectation(lambda x: abs(x - mu) ** 3)
            assert tail2 <= tail3 / eta
            exact_assertions += 1

    constants = exact_constant_checks()
    exact_assertions += 4

    pairwise = [pairwise_independent_row(m) for m in (2, 3, 5, 8)]
    exact_assertions += 4 * 2

    nonconverse = [lindeberg_not_lyapunov_row(m) for m in (2, 3, 5, 10, 25)]
    exact_assertions += 5

    local = [
        binomial_local_diagnostic(100, Q(1, 2), 50),
        binomial_local_diagnostic(200, Q(1, 3), 67),
        binomial_local_diagnostic(500, Q(2, 5), 205),
    ]
    for d in local:
        if d["proved_log_ratio_bound"] is not None and d["proved_log_ratio_bound"] <= 1:
            assert d["relative_error"] <= d["derived_relative_bound_if_log_le_1"] + 1e-12
            diagnostic_checks += 1

    # Rare-spike diagnostic refuting a universal n=30 rule.
    rare = FiniteLaw({Q(-100): Q(1, 20000), Q(0): Q(9999, 10000), Q(100): Q(1, 20000)})
    rare30 = rare.iid_sum(30)
    atom0 = rare30.mass.get(Q(0), Q(0))
    all_zero = Q(9999, 10000) ** 30
    assert atom0 >= all_zero
    exact_assertions += 1
    assert all_zero > Q(997, 1000)
    exact_assertions += 1

    return {
        "status": "passed",
        "exact_assertions": exact_assertions,
        "floating_diagnostic_checks": diagnostic_checks,
        "constant_checks": constants,
        "finite_law_diagnostics": diagnostics,
        "binomial_local_diagnostics": local,
        "pairwise_independence_counterexample": pairwise,
        "lindeberg_not_lyapunov_counterexample": nonconverse,
        "rare_spike_n30": {
            "all_zero_probability_exact": str(all_zero),
            "all_zero_probability_float": float(all_zero),
            "atom_at_zero_exact": str(atom0),
            "continuous_target_kolmogorov_lower_bound_from_atom": float(atom0) / 2.0,
        },
        "notes": [
            "The exact_assertions count includes only integer/Fraction identities and inequalities.",
            "Gaussian CDF and local Gaussian values are floating-point regression diagnostics only.",
            "Finite validation is not a proof of the universal theorems or an iPRA derivation.",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default="validation.json")
    args = parser.parse_args()
    result = run_validation()
    with open(args.output, "w", encoding="utf-8") as f:
        json.dump(result, f, indent=2, sort_keys=True)
        f.write("\n")
    print(json.dumps({
        "status": result["status"],
        "exact_assertions": result["exact_assertions"],
        "floating_diagnostic_checks": result["floating_diagnostic_checks"],
    }))


if __name__ == "__main__":
    main()
