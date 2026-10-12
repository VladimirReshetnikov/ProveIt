#!/usr/bin/env python3
"""Reproducible diagnostics for quadratic polylogarithmic feedback.

This program uses positive finite recurrences.  Floating-point comparisons
are diagnostics, not interval certificates.  The exact rational check uses
the original implicit equation independently of Lagrange inversion.

Dependencies: Python >=3.10, numpy, mpmath.
Default output: feedback_numerics/ beside this script.
"""

from __future__ import annotations

import argparse
import csv
from fractions import Fraction
import json
from pathlib import Path
import platform
import time

import mpmath as mp
import numpy as np


mp.mp.dps = 75
LD = np.longdouble


def ld(x):
    return LD(mp.nstr(x, 40))


def number(x, digits=20):
    if isinstance(x, np.generic):
        return np.format_float_scientific(x, precision=digits, unique=False)
    return mp.nstr(x, digits)


def exp_fraction(a, scalar, n):
    """Exact [t^0,...,t^n] exp(scalar*a(t)), a(0)=0."""
    e = [Fraction(0)] * (n + 1)
    e[0] = Fraction(1)
    for k in range(1, n + 1):
        e[k] = scalar * sum(Fraction(j) * a[j] * e[k - j]
                            for j in range(1, k + 1)) / k
    return e


def exact_rational_check(nmax=8):
    """Compare original equation to Lagrange, at integer s=3,u=4."""
    s, u = 3, Fraction(4)
    f = [Fraction(0)] * (nmax + 1)
    original = [Fraction(0)] * (nmax + 1)
    lagrange = [Fraction(0)] * (nmax + 1)
    for n in range(1, nmax + 1):
        f[n] = (Fraction(1, n**s)
                + sum((f[j] * f[n-j] for j in range(1, n)), Fraction(0)) / 2) / u
        rhs = sum((original[j] * original[n-j]
                   for j in range(1, n)), Fraction(0)) / 2
        for j in range(1, n + 1):
            rhs += exp_fraction(original, Fraction(j), n-j)[n-j] / j**s
        original[n] = rhs / u
        lagrange[n] = exp_fraction(f, Fraction(n), n)[n] / n
    assert original == lagrange
    assert all(c > 0 for c in original[1:])
    return {
        "s": s, "u": str(u), "degrees_checked": nmax,
        "all_original_equation_coefficients_equal_lagrange": True,
        "all_checked_coefficients_positive": True,
        "coefficients": [str(x) for x in original[1:]],
    }


def f_coefficients(s, u, nmax):
    """Positive convolution from u*f-f^2/2=Li_s(t)."""
    a = np.zeros(nmax + 1, dtype=LD)
    nn = np.arange(1, nmax + 1, dtype=LD)
    tail = nn ** (-ld(s))
    ul = ld(u)
    for n in range(1, nmax + 1):
        a[n] = (tail[n-1]
                + LD("0.5") * np.dot(a[1:n], a[n-1:0:-1])) / ul
    assert np.all(a[1:] > 0)
    return a


def poisson_coefficient(f, n, tau, f_tau):
    """Return R^n*v_n via a tilted positive probability recurrence.

    R=tau*exp(-f(tau)), and the Poisson jump intensities are
    n*f_j*tau^j.  No asymptotic value enters this recurrence.
    """
    powers = ld(tau) ** np.arange(n+1, dtype=LD)
    j = np.arange(n+1, dtype=LD)
    weighted = j * f[:n+1] * powers
    e = np.zeros(n+1, dtype=LD)
    e[0] = np.exp(-LD(n) * ld(f_tau))
    if e[0] == 0:
        # On Windows longdouble often has binary64's exponent range.  Work
        # with a common moving scale, then apply the Poisson normalization
        # in the logarithm.  All finite recurrence terms remain positive.
        e[0] = LD(1)
        log_scale = LD(0)
        threshold = LD("1e100")
        factor = LD("1e-100")
        log_step = LD(100)*np.log(LD(10))
        for k in range(1, n+1):
            e[k] = (LD(n) / LD(k)) * np.dot(weighted[1:k+1], e[k-1::-1])
            if e[k] > threshold:
                e[:k+1] *= factor
                log_scale += log_step
        result = np.exp(np.log(e[n])+log_scale-LD(n)*ld(f_tau))/LD(n)
        assert np.isfinite(result) and result > 0
        return result
    for k in range(1, n+1):
        e[k] = (LD(n) / LD(k)) * np.dot(weighted[1:k+1], e[k-1::-1])
    assert np.isfinite(e[n]) and e[n] > 0
    return e[n] / LD(n)


def interior_parameters(s, u):
    lo, hi = mp.mpf(0), mp.mpf(1)
    for _ in range(260):
        tau = (lo + hi) / 2
        value = 2*mp.polylog(s, tau) + mp.polylog(s-1, tau)**2
        if value < u*u:
            lo = tau
        else:
            hi = tau
    tau = (lo + hi) / 2
    w = mp.polylog(s-1, tau)
    v = u-w
    residual = (2*mp.polylog(s, tau)+w*w-u*u) / (1+u*u)
    return tau, v, w, residual


def make_cases():
    cases = []
    for sval in ["2.5", "3", "4"]:
        s = mp.mpf(sval)
        a = mp.zeta(s-1)
        uc = mp.sqrt(2*mp.zeta(s)+a*a)
        cases.append(dict(name=f"critical_s_{sval}", regime="critical",
                          s=s, u=uc, A=a, b=a, tau=mp.mpf(1),
                          f_tau=uc-a, R=mp.exp(a-uc)))
    for sval in ["2.5", "4"]:
        s = mp.mpf(sval)
        a = mp.zeta(s-1)
        b = 2*a
        u = mp.sqrt(2*mp.zeta(s)+b*b)
        cases.append(dict(name=f"supercritical_s_{sval}",
                          regime="supercritical", s=s, u=u, A=a, b=b,
                          tau=mp.mpf(1), f_tau=u-b, R=mp.exp(b-u)))
    for sval in ["2.5", "3", "4"]:
        s = mp.mpf(sval)
        a = mp.zeta(s-1)
        uc = mp.sqrt(2*mp.zeta(s)+a*a)
        u = mp.mpf("0.8")*uc
        tau, v, w, residual = interior_parameters(s, u)
        cases.append(dict(name=f"interior_s_{sval}", regime="interior",
                          s=s, u=u, A=a, tau=tau, f_tau=v,
                          w=w, R=tau*mp.exp(-v),
                          normalized_characteristic_residual=residual))
    return cases


def leading(case, n):
    s, a = case["s"], case["A"]
    if case["regime"] == "interior":
        c = mp.sqrt(case["w"] /
                    (2*mp.pi*(1+mp.polylog(s-2, case["tau"]))))
        return c*mp.mpf(n)**mp.mpf("-1.5")
    if case["regime"] == "supercritical":
        b = case["b"]
        c = b**(s-1)/(b-a)**s
        return c*mp.mpf(n)**(-s)
    if s < 3:
        alpha = 1/(s-1)
        c = (a/mp.gamma(1-s))**alpha/(-mp.gamma(-alpha))
        return c*mp.mpf(n)**(-1-alpha)
    if s == 3:
        return mp.sqrt(a/mp.pi)*mp.mpf(n)**mp.mpf("-1.5")/mp.sqrt(mp.log(n))
    c = mp.sqrt(a/(2*mp.pi*(1+mp.zeta(s-2))))
    return c*mp.mpf(n)**mp.mpf("-1.5")


def s3_refinements(n, a):
    l = mp.log(n)
    base = mp.sqrt(a/mp.pi)*mp.mpf(n)**mp.mpf("-1.5")/mp.sqrt(l)
    h = mp.log(l)+3+mp.euler-mp.log(a)
    correction = -h/(2*l)
    second = (3*h*h/8-h/2-3*mp.pi**2/16-mp.mpf("1.5"))/(l*l)
    lam = -mp.lambertw(-2*a*mp.exp(-5)/n, -1)
    an = mp.sqrt(mp.mpf(n)*lam/(2*a))
    c1 = (2-mp.euler-mp.log(2))/2
    d = mp.euler+mp.log(2)
    c2 = 1-2*d+3*d*d/8-3*mp.pi**2/16
    return {
        "ordinary_log_first_correction": base*(1+correction),
        "ordinary_log_second_correction": base*(1+correction+second),
        "lambert_normal_scale": lam,
        "normal_first_correction": (1+c1/lam)/(n*an*mp.sqrt(2*mp.pi)),
        "normal_second_correction":
            (1+c1/lam+c2/lam**2)/(n*an*mp.sqrt(2*mp.pi)),
    }


def mp_check(case, n=64):
    s, u = case["s"], case["u"]
    f = [mp.mpf(0)] * (n+1)
    for k in range(1, n+1):
        f[k] = (mp.mpf(k)**(-s)
                + mp.fsum(f[j]*f[k-j] for j in range(1,k))/2)/u
    e = [mp.mpf(0)] * (n+1)
    e[0] = mp.exp(-n*case["f_tau"])
    for k in range(1,n+1):
        e[k] = mp.mpf(n)/k*mp.fsum(
            j*f[j]*case["tau"]**j*e[k-j] for j in range(1,k+1))
    exact_mp = e[n]/n
    fl = f_coefficients(s,u,n)
    result_ld = poisson_coefficient(fl,n,case["tau"],case["f_tau"])
    error = mp.mpf(str(result_ld))/exact_mp-1
    tolerance = (mp.mpf("2e-15") if np.finfo(LD).precision >= 18
                 else mp.mpf("2e-13"))
    assert abs(error) < tolerance
    return {
        "case": case["name"], "n": n, "mpmath_digits": mp.mp.dps,
        "mpmath_scaled_coefficient": number(exact_mp,55),
        "longdouble_scaled_coefficient": number(result_ld),
        "relative_difference": number(error),
        "agreement_better_than_2e_minus_15": bool(abs(error)<mp.mpf("2e-15")),
        "acceptance_tolerance":number(tolerance),
        "agreement_within_tolerance":True,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--indices", default="128,512,2048")
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parent/"feedback_numerics")
    args = parser.parse_args()
    indices = sorted(set(int(n) for n in args.indices.split(",")))
    if not indices or min(indices)<2:
        parser.error("indices must be comma-separated integers at least 2")
    started = time.perf_counter()
    cases = make_cases()
    exact = exact_rational_check()
    check = mp_check(cases[1])
    rows = []
    metadata = []
    for case in cases:
        f = f_coefficients(case["s"], case["u"], max(indices))
        metadata.append({k: number(v,35) if isinstance(v,mp.mpf) else v
                         for k,v in case.items()})
        for n in indices:
            actual = poisson_coefficient(f,n,case["tau"],case["f_tau"])
            asymptotic = leading(case,n)
            row = {
                "case": case["name"], "regime": case["regime"],
                "s": number(case["s"]), "n": n,
                "scaled_coefficient": number(actual),
                "scaled_leading": number(asymptotic),
                "ratio_to_leading": number(actual/ld(asymptotic)),
            }
            if case["s"] == 3 and case["regime"] == "critical":
                refinement=s3_refinements(n,case["A"])
                row.update({
                    "ratio_to_log_refinement": number(
                        actual/ld(refinement["ordinary_log_first_correction"])),
                    "ratio_to_second_log_refinement": number(
                        actual/ld(refinement["ordinary_log_second_correction"])),
                    "ratio_to_lambert_normal_refinement": number(
                        actual/ld(refinement["normal_first_correction"])),
                    "ratio_to_lambert_second_refinement": number(
                        actual/ld(refinement["normal_second_correction"])),
                    "lambert_normal_scale": number(refinement["lambert_normal_scale"]),
                })
            rows.append(row)
        print(case["name"], ", ".join(
            f"n={r['n']}: {r['ratio_to_leading']}"
            for r in rows if r["case"]==case["name"]), flush=True)
    results = {
        "status": "completed: exact assertions and floating-point diagnostics",
        "not_an_interval_certificate": True,
        "environment": {"python":platform.python_version(),
                        "numpy":np.__version__, "mpmath":mp.__version__,
                        "longdouble_precision_digits":int(np.finfo(LD).precision),
                        "longdouble_min_exponent":int(np.finfo(LD).minexp)},
        "indices": indices, "exact_rational_check":exact,
        "independent_precision_check":check, "cases":metadata,
        "coefficient_phase_rows":rows,
        "elapsed_seconds":time.perf_counter()-started,
    }
    args.output_dir.mkdir(parents=True,exist_ok=True)
    with (args.output_dir/"verification.json").open("w",encoding="utf-8",newline="\n") as fh:
        json.dump(results,fh,indent=2,ensure_ascii=False)
        fh.write("\n")
    fieldnames=list(rows[0]) + ["ratio_to_log_refinement", "ratio_to_second_log_refinement",
        "ratio_to_lambert_normal_refinement", "ratio_to_lambert_second_refinement",
        "lambert_normal_scale"]
    with (args.output_dir/"coefficient_phases.csv").open("w",encoding="utf-8",newline="") as fh:
        writer=csv.DictWriter(fh,fieldnames=fieldnames,lineterminator="\n")
        writer.writeheader();writer.writerows(rows)
    print(f"Completed in {results['elapsed_seconds']:.2f} seconds. Output: {args.output_dir}")


if __name__ == "__main__":
    main()
