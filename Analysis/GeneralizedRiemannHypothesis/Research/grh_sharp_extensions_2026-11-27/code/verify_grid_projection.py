#!/usr/bin/env python3
"""Independent checks for the finite positive grid projection theorem.

The exact checks use two independent formulas for convolution weights.
The high-precision and finite-grid checks are numerical diagnostics, not proofs
about the zeros of any L-function. The prime demonstration evaluates the
finite arithmetic statistic directly; it uses no zeros or L-value routine.
"""
from __future__ import annotations

import argparse
import bisect
import cmath
import json
import math
import platform
from pathlib import Path

import mpmath as mp


def convolution_counts(k: int, m: int) -> list[int]:
    counts = [1]
    for _ in range(m):
        nxt = [0] * (len(counts) + k)
        running = 0
        for j in range(len(nxt)):
            if j < len(counts):
                running += counts[j]
            if 0 <= j - k - 1 < len(counts):
                running -= counts[j - k - 1]
            nxt[j] = running
        counts = nxt
    return counts


def inclusion_exclusion_count(k: int, m: int, j: int) -> int:
    if m == 0:
        return int(j == 0)
    return sum(
        (-1) ** a * math.comb(m, a)
        * math.comb(j - a * (k + 1) + m - 1, m - 1)
        for a in range(min(m, j // (k + 1)) + 1)
    )


def exact_checks() -> dict:
    cases = []
    coefficients = 0
    for k in (1, 2, 3, 8, 16, 32, 64):
        for m in (0, 1, 2, 4, 7, 12):
            counts = convolution_counts(k, m)
            denom = (k + 1) ** m
            assert len(counts) == k * m + 1
            assert sum(counts) == denom
            assert all(c > 0 for c in counts)
            assert counts == counts[::-1]
            assert counts == [inclusion_exclusion_count(k, m, j)
                              for j in range(len(counts))]
            assert 2 * sum(j * c for j, c in enumerate(counts)) == m * k * denom
            second = sum(j * j * c for j, c in enumerate(counts))
            assert 12 * second == (3 * m * m * k * k + m * k * (k + 2)) * denom
            for z in (2, -1, 3):
                lhs = sum(c * z ** j for j, c in enumerate(counts))
                rhs = sum(z ** j for j in range(k + 1)) ** m
                assert lhs == rhs
            coefficients += len(counts)
            cases.append({"k": k, "m": m, "samples": len(counts),
                          "denominator_digits": len(str(denom))})
    return {"status": "passed", "cases": cases,
            "coefficient_comparisons": coefficients,
            "verified": ["independent inclusion-exclusion coefficients",
                         "positive rational weights and total mass one",
                         "reflection symmetry and exact first two moments",
                         "three exact integer polynomial evaluations"]}


def multiplier_checks() -> dict:
    mp.mp.dps = 85
    max_absolute = mp.mpf(0)
    max_relative = mp.mpf(0)
    total = 0
    for k in (2, 3, 8, 16, 32):
        for m in (1, 2, 7, 12):
            counts = convolution_counts(k, m)
            denominator = mp.mpf((k + 1) ** m)
            ws = [mp.mpc(0), mp.mpc(0, mp.mpf("1e-12")),
                  mp.mpc(0, mp.mpf("0.3")), mp.mpc(0, mp.pi),
                  mp.mpc(0, 2 * mp.pi * k),
                  mp.mpc(0, 2 * mp.pi * k + mp.mpf("0.2")),
                  mp.mpc(mp.mpf("0.2"), mp.mpf("1.3")),
                  mp.mpc(mp.mpf("-0.25"), mp.mpf("3.7"))]
            for w in ws:
                weighted = mp.fsum(mp.mpf(c) * mp.exp(w * j / k)
                                  for j, c in enumerate(counts)) / denominator
                one_step = mp.fsum(mp.exp(w * j / k) for j in range(k + 1)) / (k + 1)
                rhs = one_step ** m
                err = abs(weighted - rhs)
                max_absolute = max(max_absolute, err)
                max_relative = max(max_relative, err / max(1, abs(rhs)))
                assert err < mp.mpf("1e-70") * max(1, abs(rhs))
                total += 1
    return {"status": "passed", "precision_decimal_digits": mp.mp.dps,
            "complex_multiplier_comparisons": total,
            "max_absolute_error": str(max_absolute),
            "max_relative_error": str(max_relative)}


def contraction_checks() -> dict:
    # This finite mesh supplements, and does not replace, the analytic proof.
    maximum_ratio = 0.0
    worst = None
    total = 0
    for k in (2, 3, 4, 8, 17, 64, 257):
        for j in range(1, 6001):
            delta = math.pi * k * j / 6000
            val = abs(math.sin((k + 1) * delta / (2 * k)) /
                      ((k + 1) * math.sin(delta / (2 * k))))
            bound = (math.exp(-delta * delta / (6 * math.pi * math.pi))
                     if delta <= math.pi else
                     min(2 ** -0.5, math.pi / delta))
            ratio = val / bound
            if ratio > maximum_ratio:
                maximum_ratio = ratio
                worst = {"k": k, "delta": delta, "value": val, "bound": bound}
            assert val <= bound + 5e-13
            total += 1
        for a in (0.01, 0.25, 1.0, 7.0):
            value = math.fsum(math.exp(-a * j / k) for j in range(k + 1)) / (k + 1)
            bound = (1 + math.exp(-a)) / 2
            assert 0 < value <= bound + 1e-14
    return {"status": "passed", "mesh_comparisons": total,
            "maximum_value_to_bound_ratio": maximum_ratio, "worst_case": worst,
            "warning": "Finite numerical meshes are diagnostic, not universal certificates."}


def alias_examples() -> dict:
    mp.mp.dps = 60
    rows = []
    for k in (2, 4, 8, 16, 32, 64, 128, 256):
        gamma = 2 * mp.pi * k
        mass = int(mp.floor(mp.log(2 + gamma)))
        amplitude = 2 * mass / (mp.mpf("0.25") + gamma * gamma)
        # At every j/k, exp(+-i gamma j/k) = 1 exactly, for all j.
        rows.append({"k": k, "gamma": str(gamma), "mass_each_sign": mass,
                     "unaltered_error_at_zero": str(amplitude),
                     "error_times_k_squared_over_log_k": str(amplitude * k * k / mp.log(k))})
    return {"status": "exact identity with displayed numerical amplitudes",
            "spectrum": "Two atoms at +-2*pi*k, each of mass floor(log(2+2*pi*k)).",
            "reason": "Every lattice exponential equals one at all observations j/k.",
            "warning": "Artificial spectra; no Dirichlet zero location is claimed.",
            "examples": rows}


def primes_up_to(n: int) -> list[int]:
    marked = bytearray(b"\x01") * (n + 1)
    marked[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(n) + 1):
        if marked[p]:
            marked[p * p:n + 1:p] = b"\x00" * (((n - p * p) // p) + 1)
    return [p for p in range(2, n + 1) if marked[p]]


def prime_demonstration() -> dict:
    mp.mp.dps = 65
    max_m = 12
    cutoff = int(mp.floor(mp.exp(max_m + 1)))
    primes = primes_up_to(cutoff)
    all_powers = []
    for p in primes:
        logp = mp.log(p)
        n = p
        while n <= cutoff:
            all_powers.append((n, logp))
            n *= p
    all_powers.sort(key=lambda pair: pair[0])
    models = {
        "q4_identity": {
            "modulus": 4, "coefficient_by_residue": [0, 2, 0, 0],
            "meaning": "Principal character plus real character modulo 4.",
        },
        "q5_quartic_real_weight": {
            "modulus": 5, "coefficient_by_residue": [0, 2, 1, 1, 0],
            "meaning": "chi_0 + Re(chi) for chi(2)=i modulo 5.",
        },
    }
    result_models = {}
    for name, model in models.items():
        q = model["modulus"]
        table = model["coefficient_by_residue"]
        ns = []
        pref_a = [mp.mpf(0)]
        pref_b = [mp.mpf(0)]
        for n, logp in all_powers:
            weight = table[n % q]
            if weight:
                coeff = weight * logp
                ns.append(n)
                pref_a.append(pref_a[-1] + coeff)
                pref_b.append(pref_b[-1] + coeff / n)

        def ramp_at(t: mp.mpf) -> mp.mpf:
            x = mp.exp(t)
            j = bisect.bisect_right(ns, int(mp.floor(x)))
            return pref_b[j] - pref_a[j] / x

        ehalf = mp.exp(mp.mpf("0.5"))

        def d_at(t: mp.mpf) -> mp.mpf:
            return mp.exp((t + 1) / 2) * (1 + ramp_at(t) - ramp_at(t + 1)) / (ehalf - 1)

        rows = []
        for k in (2, 4, 8, 16, 32):
            # The largest depth is reused, so all tested averages use the same data generation.
            ds = [d_at(mp.mpf(j) / k) for j in range(max_m * k + 1)]
            for m in (2, 4, 6, 8, 10, 12):
                counts = convolution_counts(k, m)
                value = mp.fsum(mp.mpf(c) * ds[j] for j, c in enumerate(counts))
                value /= 4 * mp.mpf((k + 1) ** m)
                rows.append({"k": k, "m": m, "d_observations": m * k + 1,
                             "ramp_observations": (m + 1) * k + 1,
                             "largest_prime_power_cutoff": int(mp.floor(mp.exp(m + 1))),
                             "estimated_central_order": mp.nstr(value, 35)})
        # Compare prefix evaluation with a direct, independent finite sum at a few scales.
        direct_max_error = mp.mpf(0)
        for t in (mp.mpf("0.7"), mp.mpf("2.25"), mp.mpf("5")):
            x = mp.exp(t)
            direct = mp.fsum(table[n % q] * logp * (mp.mpf(1) / n - 1 / x)
                             for n, logp in all_powers if n <= x)
            err = abs(direct - ramp_at(t))
            direct_max_error = max(direct_max_error, err)
            assert err < mp.mpf("1e-55")
        result_models[name] = {**model, "prime_power_terms": len(ns),
                               "prefix_vs_direct_max_error": str(direct_max_error),
                               "values": rows}
    return {"status": "numerical arithmetic illustration completed",
            "precision_decimal_digits": 65, "prime_enumeration_cutoff": cutoff,
            "primes_enumerated": len(primes), "prime_powers_enumerated": len(all_powers),
            "no_zero_or_L_value_routines_used": True,
            "warning": "These decimal values do not certify central multiplicity. A rigorous stopping certificate requires error constants and a certified nonzero spectral gap.",
            "models": result_models}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("results.json"))
    parser.add_argument("--skip-primes", action="store_true")
    args = parser.parse_args()
    result = {"environment": {"python": platform.python_version(),
                              "mpmath": mp.__version__},
              "exact_weights": exact_checks(),
              "multiplier_identity": multiplier_checks(),
              "contraction": contraction_checks(),
              "alias_obstruction": alias_examples()}
    if not args.skip_primes:
        result["prime_demonstration"] = prime_demonstration()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": "passed", "output": str(args.output),
                      "exact_coefficients": result["exact_weights"]["coefficient_comparisons"],
                      "multiplier_comparisons": result["multiplier_identity"]["complex_multiplier_comparisons"],
                      "contraction_mesh_comparisons": result["contraction"]["mesh_comparisons"],
                      "prime_demonstration": not args.skip_primes}, indent=2))


if __name__ == "__main__":
    main()
