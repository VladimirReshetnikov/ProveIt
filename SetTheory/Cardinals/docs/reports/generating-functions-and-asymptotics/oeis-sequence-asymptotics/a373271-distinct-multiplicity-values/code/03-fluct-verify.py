#!/usr/bin/env python3
"""Independent finite checks and seeded diagnostics for multiplicity occupancy.

Exact verification uses Python integers and Fraction. The analytic identities
use mpmath; the finite-window and sampling diagnostics use NumPy. No numerical
experiment is used as a proof of an asymptotic statement.

Run:
    python3 code/verify.py
    python3 -O code/verify.py --skip-simulations
    python3 code/verify.py --samples 2000 --seed 2026100701

Default output is the sibling data/ directory. Re-running replaces only the
four named generated files documented below.
"""
from __future__ import annotations

import argparse
import csv
import json
import math
from collections import Counter
from fractions import Fraction
from pathlib import Path
import platform
import sys

KNOWN_D0 = [1, 2, 3, 6, 10, 14, 24, 34, 49, 70]
KNOWN_D1 = [1, 3, 5, 11, 18, 29, 48, 74, 107, 161]
EXPONENTS = (0, 1, 2)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def frac_record(value):
    return {"numerator": value.numerator, "denominator": value.denominator}


def euler_partition_numbers(limit):
    """Independent pentagonal-number recurrence."""
    p = [0] * (limit + 1)
    p[0] = 1
    for n in range(1, limit + 1):
        total = 0
        k = 1
        while k * (3 * k - 1) // 2 <= n:
            sign = 1 if k % 2 else -1
            g1, g2 = k * (3 * k - 1) // 2, k * (3 * k + 1) // 2
            total += sign * p[n - g1]
            if g2 <= n:
                total += sign * p[n - g2]
            k += 1
        p[n] = total
    return p


def enumerate_moments(n):
    """Generate each ordinary partition once as a nonincreasing part list."""
    count = 0
    first = {a: 0 for a in EXPONENTS}
    second = {a: 0 for a in EXPONENTS}
    cross01 = 0
    prefix = []

    def visit(remaining, maximum):
        nonlocal count, cross01
        if remaining == 0:
            multiplicities = set(Counter(prefix).values())
            values = {a: sum(m**a for m in multiplicities) for a in EXPONENTS}
            count += 1
            for a in EXPONENTS:
                first[a] += values[a]
                second[a] += values[a] ** 2
            cross01 += values[0] * values[1]
            return
        for part in range(min(remaining, maximum), 0, -1):
            prefix.append(part)
            visit(remaining - part, part)
            prefix.pop()

    visit(n, n)
    return count, first, second, cross01


def forbidden_coefficients(limit, forbidden):
    """Positive product DP: exclude specified exact positive multiplicities.

    At each part size j multiply by sum_{r>=0,r not forbidden} q^(jr).
    The geometric multiplication and explicit forbidden-row subtraction use
    only the previous row. This algorithm does not enumerate partitions.
    """
    previous = [1] + [0] * limit
    for part in range(1, limit + 1):
        current = previous.copy()
        for degree in range(part, limit + 1):
            current[degree] += current[degree - part]
        for multiplicity in forbidden:
            shift = part * multiplicity
            for degree in range(shift, limit + 1):
                current[degree] -= previous[degree - shift]
        require(min(current) >= 0, "Negative coefficient in positive forbidden DP")
        previous = current
    return previous


def exact_checks(limit):
    p = euler_partition_numbers(limit)
    unrestricted = forbidden_coefficients(limit, ())
    require(p == unrestricted, "Euler and product partition counts disagree")
    one = {m: forbidden_coefficients(limit, (m,)) for m in range(1, limit + 1)}
    first = {a: [0] * (limit + 1) for a in EXPONENTS}
    second = {a: [0] * (limit + 1) for a in EXPONENTS}
    cross01 = [0] * (limit + 1)
    for m in range(1, limit + 1):
        hit = [p[n] - one[m][n] for n in range(limit + 1)]
        require(min(hit) >= 0, "Negative one-bin hit count")
        for n, value in enumerate(hit):
            cross01[n] += m * value
            for a in EXPONENTS:
                first[a][n] += m**a * value
                second[a][n] += m**(2 * a) * value

    pair_count = 0
    for m in range(1, limit + 1):
        for ell in range(m + 1, limit + 1):
            two = forbidden_coefficients(limit, (m, ell))
            pair_count += 1
            for n in range(limit + 1):
                both = p[n] - one[m][n] - one[ell][n] + two[n]
                require(both >= 0, "Negative two-bin intersection coefficient")
                cross01[n] += (m + ell) * both
                for a in EXPONENTS:
                    second[a][n] += 2 * (m * ell)**a * both

    rows = []
    enumerated = 0
    for n in range(limit + 1):
        count, direct_first, direct_second, direct_cross = enumerate_moments(n)
        enumerated += count
        require(count == p[n], f"Partition count mismatch at n={n}")
        require(direct_cross == cross01[n], f"Cross moment mismatch at n={n}")
        row = {"n": n, "partitions": count, "cross_D0_D1": direct_cross}
        for a in EXPONENTS:
            require(direct_first[a] == first[a][n],
                    f"First moment mismatch: alpha={a}, n={n}")
            require(direct_second[a] == second[a][n],
                    f"Second moment mismatch: alpha={a}, n={n}")
            mean = Fraction(first[a][n], count)
            variance = Fraction(second[a][n], count) - mean**2
            require(variance >= 0, f"Negative exact variance: alpha={a}, n={n}")
            row[f"sum_D{a}"] = first[a][n]
            row[f"sum_D{a}_squared"] = second[a][n]
            row[f"mean_D{a}"] = frac_record(mean)
            row[f"variance_D{a}"] = frac_record(variance)
        rows.append(row)
    require(first[0][1:11] == KNOWN_D0, "A373271 displayed prefix mismatch")
    require(first[1][1:11] == KNOWN_D1, "A373273 displayed prefix mismatch")
    return {
        "arithmetic": "Exact Python integers and fractions.Fraction",
        "max_n": limit,
        "partitions_directly_enumerated": enumerated,
        "forbidden_singleton_products": limit,
        "forbidden_pair_products": pair_count,
        "checked_exponents": list(EXPONENTS),
        "checks": {
            "Euler_equals_unrestricted_product": True,
            "direct_equals_forbidden_first_and_second_moments": True,
            "direct_equals_forbidden_D0_D1_cross_moment": True,
            "A373271_first_10": True,
            "A373273_first_10": True,
        },
        "known_prefixes": {
            "A373271_n1_to_n10": KNOWN_D0,
            "A373273_n1_to_n10": KNOWN_D1,
        },
        "rows": rows,
    }


def analytic_checks():
    import mpmath as mp

    with mp.workdps(55):
        root2 = mp.sqrt(2)
        v_closed = mp.sqrt(mp.pi) * (
            root2 - mp.mpf(3)/4
            - 3*root2/8 * mp.log(1 + root2)
        )
        diagonal = mp.quad(
            lambda x: mp.exp(-x*x) * (-mp.expm1(-x*x))/(x*x)
            if x else mp.mpf(1), [0, 1, mp.inf]
        )
        off_diagonal = mp.sqrt(mp.pi) * mp.quad(
            lambda r: r*(1-r)/mp.sqrt(r*r+(1-r)*(1-r)), [0, 1]
        )
        v_integrals = diagonal - off_diagonal
        require(abs(v_closed - v_integrals) < mp.mpf("1e-45"),
                "Closed V0 and covariance-integral reduction disagree")
        canonical = 6**mp.mpf(".25") * v_closed/mp.sqrt(mp.pi)
        critical = (1 - mp.pi/4)/2
        v_quarter = mp.gamma(mp.mpf(".25")) * (
            (2**mp.mpf(".75") - 1)/mp.mpf("1.5")
            - mp.quad(
                lambda r: (r*(1-r))**mp.mpf(".75")
                * (r*r+(1-r)*(1-r))**mp.mpf("-.25"), [0, 1]
            )
        )
        g_mean = mp.quad(lambda u: -mp.log(u)*mp.exp(-u), [0, 1, mp.inf])
        g_second = mp.quad(
            lambda u: mp.log(u)**2*mp.exp(-u), [0, 1, mp.inf]
        )
        g_variance = g_second - g_mean**2
        require(abs(g_mean - mp.euler) < mp.mpf("1e-45"),
                "Gumbel mean integral disagrees with Euler's constant")
        require(abs(g_variance - mp.pi**2/6) < mp.mpf("1e-44"),
                "Gumbel variance integral disagrees with zeta(2)")
        d2_mean = Fraction(2, 1)
        d2_variance = Fraction(20 * 36, 90)
        require(d2_variance == 8, "D2 canonical variance simplification failed")
        means = {}
        for alpha in (mp.mpf(".25"), mp.mpf(".5"), mp.mpf(".75")):
            mellin = mp.quad(
                lambda u: u**alpha * (
                    mp.exp(-u)/(-mp.expm1(-u))**2 - 1/(u*u)
                ), [mp.mpf("1e-12"), 1, mp.inf]
            )
            # Correct the omitted tiny interval using g(u)-u^-2=-1/12+O(u^2).
            delta = mp.mpf("1e-12")
            mellin -= delta**(alpha+1)/(12*(alpha+1))
            target = mp.gamma(alpha+1)*mp.zeta(alpha)
            require(abs(mellin-target) < mp.mpf("1e-12"),
                    f"Regularized Mellin identity failed for alpha={alpha}")
            means[str(alpha)] = {
                "leading_coefficient": mp.nstr(
                    mp.gamma((1-alpha)/2)/(alpha+1), 45),
                "second_coefficient": mp.nstr(target, 45),
                "regularized_mellin_integral": mp.nstr(mellin, 35),
            }
        return {
            "arithmetic": "mpmath, 55 working decimal digits; numerical identities",
            "interval_certified": False,
            "V0_closed": mp.nstr(v_closed, 48),
            "V0_integral_reduction": mp.nstr(v_integrals, 48),
            "V0_difference": mp.nstr(v_integrals-v_closed, 12),
            "canonical_variance_coefficient_D0": mp.nstr(canonical, 48),
            "V_one_quarter": mp.nstr(v_quarter, 45),
            "critical_log_variance_coefficient": mp.nstr(critical, 45),
            "Gumbel_mean_integral": mp.nstr(g_mean, 45),
            "Gumbel_variance_integral": mp.nstr(g_variance, 45),
            "Gumbel_variance_formula": mp.nstr(mp.pi**2/6, 45),
            "D2_over_n_limiting_mean": frac_record(d2_mean),
            "D2_over_n_limiting_variance": frac_record(d2_variance),
            "weighted_mean_coefficients": means,
            "alpha1_mean_constant": mp.nstr((3-mp.euler)/2, 45),
            "alpha1_standard_Gumbel_shift": mp.nstr((3-3*mp.euler)/2, 45),
        }


def gauss_window_variance(a, b, order):
    import numpy as np

    nodes, weights = np.polynomial.legendre.leggauss(order)
    y = (b-a)*nodes/2 + (a+b)/2
    w = (b-a)*weights/2
    q = np.exp(-1/(y*y))
    diagonal = np.sum(w*q*(1-q))
    kernel = 2*q[:, None]*q[None, :]/(y[:, None]+y[None, :])**3
    off = np.sum(w[:, None]*w[None, :]*kernel)
    return float(diagonal-off)


def finite_window_checks():
    """Floating-point finite products, independently compared with the kernel."""
    import numpy as np

    a, b = 0.75, 2.5
    limit80 = gauss_window_variance(a, b, 80)
    limit160 = gauss_window_variance(a, b, 160)
    require(abs(limit80-limit160) < 2e-12, "Window quadrature failed to stabilize")
    rows = []
    for eps in (0.05, 0.025, 0.0125):
        t = eps*eps
        bins = np.arange(math.ceil(a/eps), math.floor(b/eps)+1, dtype=float)
        # j cutoff ensures each individual omitted probability is tiny.
        cutoff = math.ceil(40/(t*bins[0]))
        logq = np.zeros(len(bins))
        logratio = np.zeros((len(bins), len(bins)))
        for begin in range(1, cutoff+1, 128):
            j = np.arange(begin, min(cutoff+1, begin+128), dtype=float)
            probs = (-np.expm1(-t*j))[:, None] * np.exp(-t*j[:, None]*bins)
            logs = np.log1p(-probs)
            logq += np.sum(logs, axis=0)
            joint = probs[:, :, None] + probs[:, None, :]
            require(float(np.max(joint)) < 1, "Invalid pair probability")
            logratio += np.sum(
                np.log1p(-joint)-logs[:, :, None]-logs[:, None, :], axis=0
            )
        q = np.exp(logq)
        covariance = q[:, None]*q[None, :]*np.expm1(logratio)
        np.fill_diagonal(covariance, 0)
        variance = float(np.sum(q*(1-q))+np.sum(covariance))
        require(variance > 0, "Nonpositive finite-window variance")
        x = t*bins[0]
        omitted_bound = len(bins)*math.exp(-x*(cutoff+1))/(-math.expm1(-x))
        rows.append({
            "epsilon": eps,
            "t": t,
            "multiplicity_bins": len(bins),
            "part_size_cutoff": cutoff,
            "scaled_variance_epsilon_times_Var": eps*variance,
            "limiting_window_kernel": limit160,
            "difference": eps*variance-limit160,
            "omitted_one_bin_intensity_sum_bound_float": omitted_bound,
        })
    return {
        "scope": "Finite moving-multiplicity window, truncated part-size products",
        "arithmetic": "NumPy binary64; not interval-certified",
        "window_a": a,
        "window_b": b,
        "quadrature_order_80": limit80,
        "quadrature_order_160": limit160,
        "rows": rows,
    }


def summarize(values, target_mean, target_variance):
    import numpy as np

    values = np.asarray(values, dtype=float)
    variance = float(np.var(values, ddof=1))
    return {
        "sample_mean": float(np.mean(values)),
        "sample_variance_unbiased": variance,
        "sample_mean_standard_error": math.sqrt(variance/len(values)),
        "limiting_mean": target_mean,
        "limiting_variance": target_variance,
        "empirical_quantiles": {
            str(q): float(np.quantile(values, q, method="linear"))
            for q in (0.1, 0.25, 0.5, 0.75, 0.9)
        },
    }


def simulation_checks(samples, seed, output_dir, analytic):
    import numpy as np
    import mpmath as mp

    gamma = float(mp.euler)
    v0 = float(analytic["V0_closed"])
    critical = float(analytic["critical_log_variance_coefficient"])
    with mp.workdps(40):
        m_half = float(mp.gamma(mp.mpf(".25"))/mp.mpf("1.5"))
        c_half = float(mp.gamma(mp.mpf("1.5"))*mp.zeta(mp.mpf(".5")))
    csv_path = output_dir/"boltzmann_samples.csv"
    histogram_path = output_dir/"boltzmann_histograms.json"
    rows, histograms = [], []
    fieldnames = [
        "t", "sample", "D0", "D_half", "D1", "D2",
        "Z0_leading", "Z_half_two_term", "Z1_standard_Gumbel", "D2_over_n_eff",
    ]
    with csv_path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=fieldnames)
        writer.writeheader()
        for index, t in enumerate((1e-4, 1e-5, 1e-6)):
            eps = math.sqrt(t)
            cutoff = math.ceil(40/eps)
            j = np.arange(1, cutoff+1, dtype=float)
            success = -np.expm1(-t*j)
            rng = np.random.Generator(np.random.PCG64(seed+index))
            normalized = {key: [] for key in
                          ("Z0_leading", "Z_half_two_term",
                           "Z1_standard_Gumbel", "D2_over_n_eff")}
            for begin in range(0, samples, 32):
                batch = min(32, samples-begin)
                multiplicities = rng.geometric(success, size=(batch, cutoff))-1
                for offset, vector in enumerate(multiplicities):
                    occupied = np.unique(vector[vector > 0])
                    d0 = len(occupied)
                    dhalf = float(np.sum(np.sqrt(occupied.astype(float))))
                    d1 = sum(int(m) for m in occupied)
                    d2 = sum(int(m)**2 for m in occupied)
                    z0 = t**0.25*(d0-math.sqrt(math.pi)/eps)
                    zhalf = math.sqrt(t/math.log(1/t))*(
                        dhalf-m_half*t**(-0.75)-c_half*t**(-0.5)
                    )
                    zg = t*d1-0.5*math.log(1/t)-(3-3*gamma)/2
                    z2 = 6*t*t*d2/(math.pi*math.pi)
                    data = {
                        "t": t, "sample": begin+offset, "D0": d0,
                        "D_half": dhalf, "D1": d1, "D2": d2,
                        "Z0_leading": z0, "Z_half_two_term": zhalf,
                        "Z1_standard_Gumbel": zg, "D2_over_n_eff": z2,
                    }
                    writer.writerow(data)
                    for key in normalized:
                        normalized[key].append(data[key])
            results = {
                "Z0_leading": summarize(normalized["Z0_leading"], 0, v0),
                "Z_half_two_term": summarize(normalized["Z_half_two_term"], 0, critical),
                "Z1_standard_Gumbel": summarize(
                    normalized["Z1_standard_Gumbel"], gamma, math.pi**2/6),
                "D2_over_n_eff": summarize(normalized["D2_over_n_eff"], 2, 8),
            }
            results["correlation_Z0_Gumbel"] = float(np.corrcoef(
                normalized["Z0_leading"], normalized["Z1_standard_Gumbel"]
            )[0, 1])
            rows.append({"t": t, "part_size_cutoff": cutoff,
                         "samples": samples, "seed": seed+index, "statistics": results})
            edges_by_key = {
                "Z0_leading": np.linspace(-2.5, 2.5, 41),
                "Z_half_two_term": np.linspace(-1.5, 1.5, 41),
                "Z1_standard_Gumbel": np.linspace(-3, 8, 45),
                "D2_over_n_eff": np.linspace(0, 14, 43),
            }
            for key, edges in edges_by_key.items():
                values = np.asarray(normalized[key])
                counts, _ = np.histogram(values, edges)
                histograms.append({
                    "t": t, "statistic": key, "edges": edges.tolist(),
                    "counts": counts.tolist(), "samples": samples,
                    "below_range": int(np.sum(values < edges[0])),
                    "above_range": int(np.sum(values > edges[-1])),
                })
    histogram_path.write_text(
        json.dumps({"scope": "Seeded finite-row Boltzmann diagnostics",
                    "histograms": histograms}, indent=2)+"\n", encoding="utf-8"
    )
    return {
        "scope": "Finite-row unconditioned Boltzmann experiments; not exact-size samples",
        "proves_asymptotic_laws": False,
        "part_size_cutoff_rule": "ceil(40/sqrt(t)); omitted rows not simulated",
        "rng": "NumPy Generator(PCG64(seed + index))",
        "raw_csv": "boltzmann_samples.csv",
        "histogram_json": "boltzmann_histograms.json",
        "rows": rows,
    }


def write_exact_csv(exact, destination):
    fields = ["n", "partitions", "sum_D0", "sum_D0_squared",
              "sum_D1", "sum_D1_squared", "sum_D2", "sum_D2_squared",
              "cross_D0_D1"]
    with destination.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        for row in exact["rows"]:
            writer.writerow({key: row[key] for key in fields})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=40)
    parser.add_argument("--samples", type=int, default=2000)
    parser.add_argument("--seed", type=int, default=2026100701)
    parser.add_argument("--skip-simulations", action="store_true")
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parent.parent/"data")
    args = parser.parse_args()
    if not 10 <= args.max_n <= 45:
        parser.error("--max-n must lie between 10 and 45")
    if not 100 <= args.samples <= 10000:
        parser.error("--samples must lie between 100 and 10000")
    if not 0 <= args.seed <= 2**63-4:
        parser.error("--seed is outside the documented nonnegative range")
    import numpy as np
    import mpmath as mp
    args.output_dir.mkdir(parents=True, exist_ok=True)
    exact = exact_checks(args.max_n)
    print(f"Exact moments verified through n={args.max_n}; "
          f"{exact['partitions_directly_enumerated']} partitions enumerated", flush=True)
    analytic = analytic_checks()
    print("Covariance, Mellin and Gumbel identities checked numerically", flush=True)
    windows = finite_window_checks()
    print("Finite moving-window products evaluated", flush=True)
    result = {
        "schema": "multiplicity-occupancy-verification-v1",
        "software": {"python": platform.python_version(),
                     "numpy": np.__version__, "mpmath": mp.__version__},
        "exact": exact, "analytic": analytic, "moving_window": windows,
    }
    write_exact_csv(exact, args.output_dir/"exact_partition_moments.csv")
    if not args.skip_simulations:
        result["simulations"] = simulation_checks(
            args.samples, args.seed, args.output_dir, analytic
        )
        print(f"Completed {3*args.samples} finite-row Boltzmann samples", flush=True)
    else:
        result["simulations"] = {"skipped_by_explicit_flag": True}
    (args.output_dir/"checks.json").write_text(
        json.dumps(result, indent=2, sort_keys=True)+"\n", encoding="utf-8"
    )
    print("Wrote checks.json and exact_partition_moments.csv", flush=True)


if __name__ == "__main__":
    main()

