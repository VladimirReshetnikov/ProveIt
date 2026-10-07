#!/usr/bin/env python3
"""Supplementary finite checks for the uniform norm-limit argument.

The proofs in the article establish the general statements.  This script
checks factorial bookkeeping and smoothing under actual finite-group
relations using exact integer arithmetic, and evaluates the explicit
finite-parameter theorem with 100-digit arithmetic.  The numerical table
does not constitute an independently certified interval-arithmetic proof.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
from collections import Counter
from fractions import Fraction
from pathlib import Path
from random import Random

import mpmath as mp


def group(moduli):
    return list(itertools.product(*(range(q) for q in moduli)))


def add(a, b, moduli):
    return tuple((x + y) % q for x, y, q in zip(a, b, moduli))


def neg(a, moduli):
    return tuple((-x) % q for x, q in zip(a, moduli))


def scale(a, n, moduli):
    return tuple((n * x) % q for x, q in zip(a, moduli))


def convolve(a, b, moduli):
    result = Counter()
    for x, u in a.items():
        for y, v in b.items():
            result[add(x, y, moduli)] += u * v
    return result


def elementary(weights, degree):
    result = [1] + [0] * degree
    for w in weights:
        for j in range(degree, 0, -1):
            result[j] += w * result[j - 1]
    return result[degree]


def pairs(moduli):
    zero = (0,) * len(moduli)
    return [x for x in group(moduli) if x != zero and x < neg(x, moduli)]


def verify_moments():
    rng = Random(20261007)
    count = 0
    examples = []
    for moduli in [(3,), (5,), (7,), (9,), (3, 3), (3, 5)]:
        zero = (0,) * len(moduli)
        representatives = pairs(moduli)
        for trial in range(8):
            masses = [(x, rng.randrange(1, 5)) for x in representatives]
            masses.sort(key=lambda item: -item[1])
            autocorrelation_spectrum = Counter()
            for x, weight in masses:
                autocorrelation_spectrum[x] = weight
                autocorrelation_spectrum[neg(x, moduli)] = weight
            power = Counter({zero: 1})
            for exponent in range(1, 13):
                power = convolve(power, autocorrelation_spectrum, moduli)
                if exponent % 2:
                    continue
                r = exponent // 2
                moment = power[zero]
                for K in range(len(masses) + 1):
                    vj = [2 * weight * weight for _, weight in masses[K:]]
                    er = elementary(vj, r)
                    retained = math.factorial(2 * r) * er // (2**r)
                    assert moment >= retained
                    if vj:
                        v = sum(vj)
                        vmax = max(vj)
                        collision_lower = v**r - math.comb(r, 2) * vmax * v ** (r - 1)
                        assert math.factorial(r) * er >= collision_lower
                    count += 1
            if trial == 0:
                examples.append({"moduli": moduli, "number_of_pairs": len(masses)})
    return {"exact_moment_and_collision_checks": count, "groups": examples}


def verify_kernels():
    count = 0
    strict_alias_cases = 0
    for moduli in [(3,), (5,), (7,), (9,), (3, 3), (3, 5)]:
        zero = (0,) * len(moduli)
        reps = pairs(moduli)
        selections = [reps[:1], reps[: min(3, len(reps))], reps[:1] * 3]
        for selected in selections:
            for J in range(1, 8):
                P = Counter({zero: 1})
                for xi in selected:
                    factor = Counter(scale(xi, a, moduli) for a in range(J + 1))
                    P = convolve(P, factor, moduli)
                autocorr = convolve(P, Counter({neg(x, moduli): c for x, c in P.items()}), moduli)
                Z = autocorr[zero]
                assert Z > 0
                assert len(autocorr) <= (2 * J + 1) ** len(selected)
                assert all(c >= 0 for c in autocorr.values())
                for xi in selected:
                    multiplier = Fraction(autocorr[xi], Z)
                    assert multiplier >= Fraction(J, J + 1)
                    assert multiplier <= 1
                    count += 1
                if len(P) < (J + 1) ** len(selected):
                    strict_alias_cases += 1
    return {"exact_kernel_multiplier_checks": count, "kernels_with_aliases": strict_alias_cases}


def verify_rate_algebra():
    for r in range(16, 257):
        G = math.factorial(2 * r) // (2**r * math.factorial(r))
        assert 2 * r**r <= 3**r * G
        assert Fraction(r * (r - 1), r**3 + 1) <= Fraction(3, r)
    for k in range(10, 257):
        r = 2**k
        B = 8 * k * k + 17 * k + 3
        C = 104 * k * k + 21 * k + 7
        assert B <= r
        assert C <= r**3
        assert 2 * B - (8 * (k + 1) ** 2 + 17 * (k + 1) + 3) == 8 * k * k + k - 22
        x = Fraction(1, r)
        assert (1 + x) * (1 + 3 * x + x * x) <= 1 + 5 * x
        assert (1 + 5 * x) ** 4 <= 1 + 21 * x
    return {"exact_tail_specializations": 241, "exact_rate_parameter_checks": 247}


def evaluate_parameters():
    mp.mp.dps = 100
    rows = []
    for k in range(6, 21):
        d = 8 * k
        r = 2**k
        K = r**3
        J = r
        eta = mp.mpf(1) / r
        logL = mp.log(2 * mp.pi) + K * mp.log(2 * J + 1) + mp.log(K) + mp.log(J)
        logbeta = K * (mp.log(eta / 2) - logL)
        loggamma = logbeta - K * mp.log(d - 1)
        minus_log_F = -((d - 1) * loggamma + 2 * (logbeta - mp.log(2))) / mp.mpf(2) ** d
        activation_margin = mp.log(3) * mp.mpf(2) ** (d - 1) + logbeta - mp.log(2)
        assert activation_margin > 0
        log_G = mp.loggamma(2 * r + 1) - r * mp.log(2) - mp.loggamma(r + 1)
        tail = max(mp.mpf(r * (r - 1)) / (K + 1), mp.exp((mp.log(2) - log_G) / r))
        bound = ((1 + mp.mpf(1) / J) * (2 * eta + mp.exp(minus_log_F))) ** 4 / 3 + tail
        rows.append({
            "d": d,
            "r": r,
            "K": K,
            "J": J,
            "eta": str(Fraction(1, r)),
            "minus_log_F": mp.nstr(minus_log_F, 32),
            "tail_bound": mp.nstr(tail, 32),
            "finite_parameter_upper_bound": mp.nstr(bound, 32),
            "simple_rate_upper_bound": str(Fraction(1, 3) + Fraction(10, r)) if k >= 10 else None,
            "activation_verified_numerically": True,
        })
    return rows


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default="data/verify_norm_limit.json")
    args = parser.parse_args()
    result = {
        "status": "all supplementary checks passed",
        "scope": "General inequalities rely on the article's analytic proofs. Finite parameter decimals use 100-digit floating-point arithmetic, not certified interval arithmetic.",
        "moments": verify_moments(),
        "smoothing": verify_kernels(),
        "rate": verify_rate_algebra(),
        "finite_parameter_table": evaluate_parameters(),
    }
    path = Path(args.output)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: value for key, value in result.items() if key != "finite_parameter_table"}, indent=2))
    print(f"Wrote {len(result['finite_parameter_table'])} parameter rows to {path}")


if __name__ == "__main__":
    main()
