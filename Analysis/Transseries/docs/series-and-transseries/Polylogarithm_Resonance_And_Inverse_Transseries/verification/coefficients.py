#!/usr/bin/env python3
"""Reproducible diagnostics for inverse-polylogarithm coefficients.

Exact finite rational arithmetic checks compositional reversion.  Arbitrary
precision arithmetic compares two working precisions and the independent
localized cut integral.  None of the floating-point checks is interval
certification; the coefficient asymptotic theorems are proved in the article.
The cut integrals below have finite cutoffs and are explicitly labeled so.
"""
from __future__ import annotations

import argparse
import csv
import json
from fractions import Fraction
from pathlib import Path

import mpmath as mp
import sympy as sp


def inverse_coefficient(s: int, n: int):
    """[w^n] Li_s^{-1}(w), by the finite differential recurrence."""
    f = [mp.mpf(1) / (j + 1) ** s for j in range(n)]
    h = [mp.mpf(1)]
    for k in range(1, n):
        h.append(mp.fsum(((1-n)*j-k)*f[j]*h[k-j]
                         for j in range(1, k+1)) / k)
    return h[-1] / n


def exact_coefficients(s: int, count: int):
    values = [Fraction(0)]
    for n in range(1, count+1):
        f = [Fraction(1, (j+1)**s) for j in range(n)]
        h = [Fraction(1)]
        for k in range(1, n):
            h.append(sum((((1-n)*j-k)*f[j]*h[k-j]
                          for j in range(1, k+1)), Fraction(0)) / k)
        values.append(h[-1] / n)
    return values


def convolution(a, b, count):
    return [sum((a[j]*b[k-j] for j in range(k+1)), Fraction(0))
            for k in range(count+1)]


def exact_composition_checks(count=12):
    records = []
    for s in (2, 3, 4):
        inv = exact_coefficients(s, count)
        total = [Fraction(0)]*(count+1)
        power = [Fraction(1)]+[Fraction(0)]*count
        for j in range(1, count+1):
            power = convolution(power, inv, count)
            total = [a+b/Fraction(j**s) for a,b in zip(total, power)]
        assert total == [Fraction(0), Fraction(1)]+[Fraction(0)]*(count-1)
        records.append({"s": s, "through_degree": count,
                        "inverse_coefficients": [str(x) for x in inv[1:]],
                        "composition_identity": True})
    return records


def reciprocal_gamma_coefficients(count: int):
    """c_k from a finite formal expansion of 1/Gamma(z-k-1)."""
    answer = []
    for k in range(count):
        r = k+1
        # 1/Gamma(z-r) = z*prod_{l=1}^r(z-l)*exp(sum a_j z^j).
        a = [mp.mpf(0), mp.euler] + [(-1)**(j+1)*mp.zeta(j)/j
                                            for j in range(2, r)]
        e = [mp.mpf(1)]
        for n in range(1, r):
            e.append(mp.fsum(j*a[j]*e[n-j] for j in range(1,n+1))/n)
        p = [mp.mpf(1)]
        for l in range(1, r+1):
            q = [mp.mpf(0)]*(len(p)+1)
            for j,pj in enumerate(p):
                q[j] -= l*pj
                q[j+1] += pj
            p = q
        answer.append(-mp.fsum(p[j]*e[k-j] for j in range(k+1)))
    return answer


def exact_gamma_checks():
    z, g, z2, z3 = sp.symbols("z gamma zeta2 zeta3")
    expected = [1, 3-2*g, 6-11*g+3*g*g-3*z2,
                10-35*g+25*g*g-4*g**3+(12*g-25)*z2-8*z3]
    out = []
    for j in range(4):
        r = j+1
        exponent = g*z-z2*z**2/2+z3*z**3/3
        trunc = sp.series(sp.exp(exponent), z, 0, r).removeO()
        poly = z*sp.prod(z-l for l in range(1,r+1))
        actual = -sp.expand(poly*trunc).coeff(z,r)
        assert sp.expand(actual-expected[j]) == 0
        out.append({"j":j, "formula": str(actual), "exact_match":True})
    return out


def lambert_H(n):
    return -mp.lambertw(-mp.zeta(2)/(mp.e*n), -1).real


def scaled_cut(n, cutoff):
    """Finite local-cut contribution in units -rho^(1-n)/(n^2 H^2).

    The upper-bank value is evaluated by an exact dilogarithm reflection
    identity.  This is a local contour diagnostic, not an identity asserting
    equality to the entire coefficient at finite n.
    """
    rho, H = mp.zeta(2), lambert_H(n)
    def integrand(v):
        if not v:
            return mp.mpf(0)
        u = rho*v/(n*H)
        logx = mp.log1p(u)
        delta = -mp.polylog(2,-u)-logx*mp.log(u)+1j*mp.pi*logx
        return -H/mp.pi*mp.im(mp.exp(-n*mp.log1p(delta/rho)))
    points = [mp.mpf(0), mp.mpf("0.1"), mp.mpf(1), mp.mpf(4),
              mp.mpf(12), mp.mpf(30), mp.mpf(60), mp.mpf(100)]
    points += [mp.mpf(cutoff)]
    return mp.quad(integrand, points)


def number(x, digits=45):
    return mp.nstr(x, digits)


def write_csv(path, rows):
    with path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]))
        w.writeheader()
        w.writerows(rows)


def run(output: Path):
    output.mkdir(parents=True, exist_ok=True)
    exact = exact_composition_checks()
    gamma_exact = exact_gamma_checks()
    finite = []
    saved_s2 = {}
    for s in (2,3,4):
        for n in (96,256):
            dps_low, dps_high = n+60, n+120
            with mp.workdps(dps_low):
                low = inverse_coefficient(s,n)
            with mp.workdps(dps_high):
                high = inverse_coefficient(s,n)
                discrepancy = abs((low-high)/high)
                assert discrepancy < mp.mpf("1e-65"), (s,n,discrepancy)
                rho = mp.zeta(s)
                if s == 2:
                    H = lambert_H(n)
                    scaled = -high*n*n*H*H*rho**(n-1)
                    saved_s2[n] = scaled
                    scaling = "-a_n*n^2*H_n^2*rho^(n-1)"
                else:
                    scaled = -high*n**s*mp.zeta(s-1)**s*rho**(n-s+1)
                    scaling = "-a_n*n^s*zeta(s-1)^s*rho^(n-s+1)"
                finite.append({"s":s,"n":n,"dps_low":dps_low,
                               "dps_high":dps_high,"coefficient":number(high),
                               "relative_precision_discrepancy":number(discrepancy),
                               "scaled_coefficient":number(scaled),
                               "scaling":scaling})

    with mp.workdps(75):
        c = reciprocal_gamma_coefficients(12)
        # An independent derivative construction, well away from Gamma poles.
        gamma_numeric_error = mp.mpf(0)
        for j in range(7):
            r = j+1
            independent = -mp.im(mp.fsum(
                mp.binomial(r,l)*(-1j*mp.pi)**(r-l)*
                mp.diff(mp.gamma, r+1, l) for l in range(r+1)
            ))/(mp.pi*mp.factorial(r))
            gamma_numeric_error=max(gamma_numeric_error,abs(c[j]-independent))
        assert gamma_numeric_error < mp.mpf("1e-65")
        cuts=[]
        for n in (mp.mpf(96),mp.mpf(256),mp.mpf(10)**6,
                  mp.mpf(10)**12,mp.mpf(10)**30):
            H = lambert_H(n)
            val120, val180 = scaled_cut(n,120), scaled_cut(n,180)
            discrepancy = abs(val120-val180)
            row={"n":number(n,35),"H_n":number(H),
                 "cutoff_120":number(val120),"cutoff_180":number(val180),
                 "cutoff_difference":number(discrepancy)}
            for last in (0,2,4,6,8):
                partial=mp.fsum(c[j]/H**j for j in range(last+1))
                row[f"asymptotic_through_c{last}"]=number(partial)
                row[f"difference_through_c{last}"]=number(partial-val180)
            if int(n) in saved_s2:
                row["finite_lagrange_value"]=number(saved_s2[int(n)])
                row["local_cut_vs_finite_difference"]=number(val180-saved_s2[int(n)])
            else:
                row["finite_lagrange_value"]=""
                row["local_cut_vs_finite_difference"]=""
            cuts.append(row)
        gamma_rows=[{"j":j,"c_j":number(x)} for j,x in enumerate(c)]

    report={"status":"diagnostics completed; floating-point, not interval certified",
            "versions":{"mpmath":mp.__version__,"sympy":sp.__version__},
            "exact_composition_checks":exact,
            "exact_reciprocal_gamma_checks":gamma_exact,
            "gamma_derivative_absolute_discrepancy":number(gamma_numeric_error),
            "finite_coefficient_checks":finite,"local_cut_checks":cuts,
            "reciprocal_gamma_coefficients":gamma_rows,
            "interpretation":[
                "The composition identities and first four c_j identities are exact.",
                "Precision repetition detects cancellation error but is not interval certification.",
                "The finite local-cut integrals omit an outer contour contribution.",
                "Their finite-n agreement is diagnostic; the article proves the requisite bounds.",
                "A fixed-order asymptotic truncation need not improve at moderate n."
            ]}
    (output/"coefficients.json").write_text(json.dumps(report,indent=2)+"\n")
    write_csv(output/"finite_inverse_coefficients.csv",finite)
    write_csv(output/"dilogarithm_cut_coefficients.csv",cuts)
    write_csv(output/"reciprocal_gamma_coefficients.csv",gamma_rows)
    lines=[r"\begin{tabular}{rrr}",r"\toprule",
           r"$s$ & $n$ & Correctly normalized coefficient \\",r"\midrule"]
    for row in finite:
        lines.append(f"{row['s']} & {row['n']} & {mp.nstr(mp.mpf(row['scaled_coefficient']),12)} \\\\")
    lines += [r"\bottomrule",r"\end{tabular}"]
    (output/"coefficient_table.tex").write_text("\n".join(lines)+"\n")
    summary={"exact_composition_degrees":36,"exact_cj_formulas":4,
             "precision_repeated_finite_coefficients":len(finite),
             "finite_local_cut_comparisons":len(cuts),
             "max_precision_discrepancy":max(float(r["relative_precision_discrepancy"])
                                             for r in finite),
             "first_cj":[r["c_j"] for r in gamma_rows[:7]]}
    print(json.dumps(summary,indent=2))


if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,default=Path("build/verification"))
    args=parser.parse_args()
    run(args.output)
