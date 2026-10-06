#!/usr/bin/env python3
"""Deterministic finite audits for the Fourier and AP-count refinements.

Run from any directory. Requires NumPy; no network is used. The interval
sum is checked for every length at N=2,...,128 and several larger moduli.
The AP telescope is checked independently of its norm estimate. The
negative control demonstrates why coefficient invertibility is required.
Numerical checks supplement the article's proofs and are not formal proofs.
"""
from __future__ import annotations

import json
import math
from pathlib import Path

import numpy as np


def fourier(f: np.ndarray) -> np.ndarray:
    return np.fft.fft(f) / len(f)


def unorm(f: np.ndarray, degree: int) -> float:
    if degree == 1:
        return float(abs(np.mean(f)))
    if degree == 2:
        return float(np.sum(abs(fourier(f)) ** 4) ** .25)
    p = 2 ** (degree - 1)
    moment = np.mean([
        unorm(f * np.conj(np.roll(f, -h)), degree - 1) ** p
        for h in range(len(f))
    ])
    return float(max(0., moment) ** (1 / (2 ** degree)))


def progression(functions: list[np.ndarray]) -> complex:
    n = len(functions[0])
    x = np.arange(n)[:, None]
    r = np.arange(n)[None, :]
    prod = np.ones((n, n), dtype=complex)
    for j, f in enumerate(functions):
        prod *= f[(x + j * r) % n]
    return complex(prod.mean())


def interval_checks() -> dict:
    count = 0
    minimum_slack = float("inf")
    dual_error = 0.
    moduli = list(range(2, 129)) + [257, 509, 1009]
    rng = np.random.default_rng(20261006)
    for n in moduli:
        lengths = range(1, n) if n <= 128 else [1, 2, 7, n // 5, n // 2, n - 1]
        for m in lengths:
            indicator = np.zeros(n)
            indicator[:m] = 1
            coeff = fourier(indicator)
            beta = m / n
            b = min(beta, 1 - beta)
            total = float(np.sum(abs(coeff[1:]) ** (4 / 3)))
            upper = 4 * b ** (1 / 3) - 3 * n ** (-1 / 3)
            minimum_slack = min(minimum_slack, upper - total)
            assert total <= upper + 2e-13
            # Equality in Fourier Holder, independently reconstructed in x-space.
            extremal = np.zeros(n, dtype=complex)
            nonzero = abs(coeff) > 1e-14
            nonzero[0] = False
            extremal[nonzero] = coeff[nonzero] * abs(coeff[nonzero]) ** (-2 / 3)
            test = np.fft.ifft(extremal * n)
            assert np.max(abs(test.imag)) < 2e-12
            test = test.real
            ratio = abs(np.mean(test * indicator)) / unorm(test, 2)
            dual_error = max(dual_error, abs(ratio - total ** .75))
            assert abs(ratio - total ** .75) < 2e-11
            # A separate arbitrary centered function.
            f = rng.normal(size=n)
            f -= f.mean()
            lhs = abs(np.mean(f * indicator))
            assert lhs <= unorm(f, 2) * total ** .75 + 2e-12
            count += 1
    return {"cases": count, "minimum_spectral_sum_slack": minimum_slack,
            "maximum_dual_equality_error": dual_error,
            "all_nontrivial_lengths_checked_up_to_N": 128}


def counting_checks() -> dict:
    rng = np.random.default_rng(841006)
    count = 0
    identity_error = 0.
    minimum_slack = float("inf")
    for n, k in [(5, 3), (5, 4), (5, 5), (7, 3), (7, 4), (7, 5),
                 (9, 3), (11, 4), (13, 5), (15, 3), (25, 4)]:
        assert math.gcd(n, math.factorial(k - 1)) == 1
        for case in range(12):
            gs = [rng.random(n) for _ in range(k)]
            if case % 3 == 0:
                gs = [(g > rng.uniform(.15, .85)).astype(float) for g in gs]
            delta = [float(g.mean()) for g in gs]
            fs = [g - d for g, d in zip(gs, delta)]
            exact = progression(gs)
            main = math.prod(delta)
            telescope = complex(main)
            bound = 0.
            for j in range(3, k + 1):
                suffix = math.prod(delta[j:])
                telescope += suffix * progression(gs[:j - 1] + [fs[j - 1]])
                bound += suffix * unorm(fs[j - 1], j - 1)
            identity_error = max(identity_error, abs(exact - telescope))
            assert abs(exact - telescope) < 2e-12
            slack = bound - abs(exact - main)
            minimum_slack = min(minimum_slack, slack)
            assert slack >= -2e-12
            # Direct endpoint GvN for unrelated complex bounded functions.
            functions = [rng.random(n) * np.exp(2j * np.pi * rng.random(n))
                         for _ in range(k)]
            assert abs(progression(functions)) <= unorm(functions[-1], k - 1) + 2e-12
            count += 1
    f = np.array([1., 1., -1.])
    lhs = abs(progression([f, np.ones(3), np.ones(3), f]))
    rhs = unorm(f, 3)
    assert lhs > rhs + 1e-6
    return {"cases": count, "maximum_telescope_identity_error": identity_error,
            "minimum_counting_bound_slack": minimum_slack,
            "invertibility_negative_control": {"N": 3, "k": 4,
                "f1_and_f4": f.tolist(), "f2_and_f3": [1, 1, 1],
                "progression_average": lhs, "U3_of_f4": rhs,
                "invalid_without_coefficient_hypothesis": True}}


def spectral_deficit_checks() -> dict:
    rng = np.random.default_rng(731006)
    cases = 0
    equality_error = 0.
    for n in [3, 5, 7, 11, 17, 31]:
        for j in range(31):
            f = rng.normal(size=n) if j else np.eye(1, n, 0)[0] * n - 1
            f -= f.mean()
            coeff = fourier(f)
            b = abs(coeff) ** 2
            b[0] = 0
            sigma2 = float(b.sum())
            rho4 = float((b * b).sum())
            B1 = sum(b[r] * b[s] * b[(r + s) % n]
                     for r in range(n) for s in range(n))
            upper = sigma2 * rho4 - rho4 ** 2 / sigma2
            assert B1 <= upper + 1e-10 * max(1., upper)
            if j == 0:
                equality_error = max(equality_error, abs(B1 - upper))
                assert abs(B1 - upper) < 1e-9
            cases += 1
    return {"cases": cases, "flat_spectrum_equality_error": equality_error}


def main() -> None:
    result = {"status": "passed", "scope": "finite numerical checks, not formal verification",
              "numpy_version": np.__version__,
              "intervals": interval_checks(), "counting": counting_checks(),
              "spectral_deficit": spectral_deficit_checks()}
    destination = Path(__file__).with_name("fourier_counting_summary.json")
    destination.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
