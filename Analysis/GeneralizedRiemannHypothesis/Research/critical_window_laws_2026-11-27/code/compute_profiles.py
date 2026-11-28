#!/usr/bin/env python3
"""Certified critical-window profiles for hidden alternating forms.

Only mpmath is required. All numerical sums use its outward-rounded
interval arithmetic. The infinite products are enclosed with the elementary
product/union bound; the dimension sum is truncated using the theorem's
Gaussian-moment tail bound. Each printed decimal is verified to lie within
the stated absolute error of the full infinite expression.

This certifies evaluations of the proved limit formula. It is not a finite-n
error bound and is not evidence in place of the asymptotic proof.
"""

from __future__ import annotations

import csv
import json
from pathlib import Path

import mpmath as mp


mp.mp.dps = 120
mp.iv.dps = 100
IV = mp.iv
PRODUCT_TERMS = 400
TAIL_TARGET = mp.mpf("1e-70")
PRINTED_ABSOLUTE_ERROR = mp.mpf("1e-45")


def endpoints(x):
    """Exact binary interval endpoints converted at higher working precision."""
    return mp.mpf(x._mpi_[0]), mp.mpf(x._mpi_[1])


def enclose_endpoints(lower, upper):
    return IV.mpf([lower.a, upper.b])


def add_unknown_positive_tail(x, tail):
    return enclose_endpoints(x, x + tail)


def certified_decimal(x):
    lo, hi = endpoints(x)
    printed = mp.nstr((lo + hi) / 2, 55)
    center = IV.mpf(printed)
    bound = IV.mpf("1e-45")
    enclosure = center + IV.mpf([-bound.b, bound.b])
    elo, ehi = endpoints(enclosure)
    assert elo <= lo <= hi <= ehi, (printed, lo, hi)
    return printed


def constants(q: int):
    iq = IV.mpf(q)
    g = [IV.mpf(1)]
    for j in range(1, PRODUCT_TERMS + 1):
        g.append(g[-1] * (1 - iq ** (-j)))
    g_tail = iq ** (-PRODUCT_TERMS) / (q - 1)
    gamma = enclose_endpoints(g[-1] * (1 - g_tail), g[-1])
    beta_upper = IV.mpf(1)
    for j in range(1, PRODUCT_TERMS + 1):
        beta_upper *= 1 - iq ** (-(2 * j - 1))
    beta_tail = iq ** (-(2 * PRODUCT_TERMS + 1)) / (1 - iq ** (-2))
    beta = enclose_endpoints(beta_upper * (1 - beta_tail), beta_upper)
    c = beta / (1 - 1 / iq)
    return iq, g, gamma, beta, c


def one_profile(q: int, a: int, const):
    iq, g, gamma, beta, c = const
    lam = c * iq ** (-a)
    llo, lhi = endpoints(lam)
    assert mp.floor(llo) == mp.floor(lhi), "Increase precision: ambiguous cutoff"
    z_cut = int(mp.floor(llo))
    k_min = max(0, 1 - a)
    r = max(k_min + 1, 1)
    while True:
        tail = iq ** (-r * (r + a - 1)) / g[r]
        if endpoints(tail)[1] < TAIL_TARGET:
            break
        r += 1
        assert r < PRODUCT_TERMS

    full_tv_sum = IV.mpf(0)
    void_sum = IV.mpf(0)
    single_sum = IV.mpf(0)
    mass_sum = IV.mpf(0)
    for k in range(k_min, r):
        pk = gamma * iq ** (-k * (k + a - 1)) / (g[k] * g[k + a - 1])
        m = (q**k - 1) // (q - 1)
        p0 = (1 - beta) ** m
        void_sum += pk * p0
        mass_sum += pk
        if m:
            single_sum += pk * m * beta * (1 - beta) ** (m - 1)
        pz = p0
        hinge = pz
        for z in range(1, min(m, z_cut) + 1):
            pz *= IV.mpf(m - z + 1) / z * beta / (1 - beta)
            hinge += pz * (1 - IV.mpf(z) / lam)
        full_tv_sum += pk * hinge

    mass = add_unknown_positive_tail(mass_sum, tail)
    mlo, mhi = endpoints(mass)
    assert mlo <= 1 <= mhi
    full_tv = add_unknown_positive_tail(full_tv_sum, tail)
    void = add_unknown_positive_tail(void_sum, tail)
    single = add_unknown_positive_tail(single_sum, tail)
    recovery = (1 - void) / lam
    uniqueness = single / lam
    if a >= 0:
        flo, fhi = endpoints(full_tv)
        vlo, vhi = endpoints(void)
        assert max(flo, vlo) <= min(fhi, vhi)
        elimination = gamma / g[a]
    else:
        elimination = IV.mpf(0)
    dim_tv = (
        iq ** (a - 1) * gamma / g[1 - a]
        if a <= 0 else gamma / g[a - 1]
    )
    assert endpoints(full_tv - dim_tv)[0] > 0
    quantities = {
        "lambda": lam,
        "full_tv": full_tv,
        "dimension_tv": dim_tv,
        "equal_prior_error": (1 - full_tv) / 2,
        "optimal_recovery": recovery,
        "unique_nondegenerate_probability": uniqueness,
        "elimination_recovery": elimination,
        "null_void_probability": void,
    }
    result = {"q": q, "a": a}
    result.update({key: certified_decimal(val) for key, val in quantities.items()})
    result.update({
        "absolute_error_bound": "1e-45",
        "dimension_cutoff_exclusive": r,
        "dimension_tail_upper": mp.nstr(endpoints(tail)[1], 30),
    })
    return result


def main():
    base = Path(__file__).resolve().parents[1]
    data = base / "results"
    data.mkdir(parents=True, exist_ok=True)
    rows = []
    const_output = []
    for q in (2, 3, 4, 5):
        const = constants(q)
        _, _, gamma, beta, c = const
        const_output.append({
            "q": q,
            "gamma": certified_decimal(gamma),
            "beta": certified_decimal(beta),
            "c": certified_decimal(c),
            "absolute_error_bound": "1e-45",
        })
        for a in range(-5, 6):
            row = one_profile(q, a, const)
            rows.append(row)
            print(f"q={q}, a={a:+d}: TV={mp.nstr(mp.mpf(row['full_tv']), 18)}, "
                  f"recovery={mp.nstr(mp.mpf(row['optimal_recovery']), 18)}")
    document = {
        "meaning": "Limits as even n tends to infinity, t=binom(n,2)-1+a; fixed q,a.",
        "arithmetic": "mpmath.iv, 100 decimal working digits, outward rounding",
        "product_terms": PRODUCT_TERMS,
        "product_bound": "partial_product*(1-sum_of_omitted_factors) <= product <= partial_product",
        "dimension_tail_bound": "q^(-r*(r+a-1))/prod_{j=1}^r(1-q^-j)",
        "constants": const_output,
        "profiles": rows,
    }
    (data / "profiles.json").write_text(json.dumps(document, indent=2) + "\n")
    with (data / "profiles.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    table = [
        r"\begin{tabular}{rrrrrr}",
        r"\toprule",
        r"$q$ & $a$ & Full TV & Dimension TV & Optimal recovery & Elimination \\",
        r"\midrule",
    ]
    for row in rows:
        vals = [str(row["q"]), str(row["a"])] + [
            f"{float(row[key]):.9f}" for key in
            ("full_tv", "dimension_tv", "optimal_recovery", "elimination_recovery")
        ]
        table.append(" & ".join(vals) + r" \\")
    table += [r"\bottomrule", r"\end{tabular}"]
    (data / "profile_table.tex").write_text("\n".join(table) + "\n")
    print("ALL_PROFILE_INTERVAL_CHECKS_PASSED: 44 profiles, absolute error <= 1e-45")


if __name__ == "__main__":
    main()
