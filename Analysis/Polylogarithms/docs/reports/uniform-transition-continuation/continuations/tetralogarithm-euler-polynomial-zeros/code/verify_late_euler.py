#!/usr/bin/env python3
"""Independent diagnostics for the late-Euler theorem.

The proof is in ../sections/04_extremal.tex. These computations are corroboration,
not certificates for the analytic asymptotic assertions. Dependencies:
mpmath, sympy. Run with --quick for the symbolic audit and a short table.
"""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path

import mpmath as mp
import sympy as sp


def symbolic_checks() -> dict[str, bool]:
    x, n = sp.symbols("x n", positive=True)
    wn = (1-x)**n/(1+x)
    # The derivative numerator for the tilted defect used to localize b.
    poly = 1 + 2*(n+1)*x + (2*n-3)*x*x
    log_numerator = sp.expand(
        -(n-1)*(1+x)*poly
        + (1-x)*(1+x)*sp.diff(poly, x)
        - 2*(1-x)*poly
    )
    claimed = (n+1 - (2*n*n+n+5)*x
               - (4*n*n-3*n-7)*x*x
               - (2*n-3)*(n-1)*x**3)
    assert sp.expand(log_numerator-claimed) == 0
    # The derivative sign polynomial of the axis kernel.
    kn = (1+x)*(1-x*x)**(n-1)/(1+x*x)
    sign_poly = 1-(2*n+1)*x+x*x-(2*n-3)*x**3
    check = sp.cancel(1/(1+x)-2*(n-1)*x/(1-x*x)-2*x/(1+x*x)
                      - sign_poly/((1-x*x)*(1+x*x)))
    assert check == 0
    for ni in (2, 3, 4, 17):
        w = wn.subs(n, ni)
        bfun = ((1-x)**(ni-1)
                * (1+2*(ni+1)*x+(2*ni-3)*x*x)/(1+x)**2)
        assert sp.factor((1-w)+2*x*sp.diff(w, x) - (1-bfun)) == 0
    return {"tilted_defect_polynomial": True,
            "axis_derivative_polynomial": True,
            "tilted_defect_derivative": True}


def scaled_h(n: mp.mpf, t: mp.mpf) -> mp.mpf:
    """((1-t/n)^(n-1)/(1+t/n))-1+t, without small-t cancellation."""
    if t == 0:
        return mp.mpf(0)
    if t >= n:
        return t-1
    if t >= mp.mpf("0.25"):
        if t > 300:  # error < exp(-300), far below working precision
            return t-1
        s = t/n
        return mp.exp((n-1)*mp.log1p(-s)-mp.log1p(s))-1+t
    # d_j = n^(-j) sum_{k=0}^j binomial(n-1,k), so
    # P_n(t/n) = sum_j (-1)^j d_j t^j.
    binom_scaled = (n-1)/n
    d = mp.mpf(1)
    result = mp.mpf(0)
    power = -t
    for j in range(2, 300):
        binom_scaled *= (1-j/n)/j
        d = binom_scaled+d/n
        power *= -t
        term = d*power
        result += term
        if abs(term) < mp.eps*abs(result)/10:
            return result
    raise ArithmeticError("small-t series failed to converge")


def centered_correction(n: mp.mpf, b: mp.mpf) -> tuple[mp.mpf, mp.mpf]:
    ell = mp.log(n)
    t0 = ell/2
    psi = mp.digamma(b)
    log_prefactor = (b-1)*mp.log(t0)-t0-mp.loggamma(b)

    def integrand(y: mp.mpf) -> mp.mpc:
        total = t0+y
        if total <= 0:
            return mp.mpc(0)
        t = mp.exp(-2*y)
        logr = (b-1)*mp.log1p(y/t0)-y
        factor = (mp.exp(logr)*(1+mp.exp(-total))
                  * scaled_h(n, t))
        return factor*mp.mpc(1, mp.log(total)-psi)

    cuts = [-t0]
    cuts.extend(mp.mpf(v) for v in (-10, 0, 10, 40, 100, 300)
                if mp.mpf(v) > -t0)
    cuts.append(mp.inf)
    value = mp.quad(integrand, cuts)
    prefactor = mp.exp(log_prefactor)
    return prefactor*value.real, prefactor*value.imag


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--optimizers", action="store_true",
                        help="also tabulate finite-N axis maxima")
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    mp.mp.dps = 50
    L = mp.log(mp.mpf(3)/2)
    B = 1/L
    p = B*mp.log(2)
    q = mp.log(3)/mp.log(2)
    d0 = B*mp.log(q)
    c = (1-1/q)*q**(-p)
    nu = B-mp.mpf("0.5")
    I = mp.mpf("0.5")-B+B*mp.log(2*B)
    D = mp.sqrt(B/(2*mp.pi))*mp.gamma(-nu)*(2*B)**(-d0)
    K = mp.log(2*B)*D/(mp.log(2)*L*q**(-p))
    results = {"symbolic_checks": symbolic_checks(),
               "constants": {k: mp.nstr(v, 40) for k, v in
                             dict(B=B, p=p, q=q, d0=d0, c=c,
                                  nu=nu, I=I, D=D, K=K).items()},
               "explicit_threshold_checks": {
                   "bounded_b_upper": mp.nstr(800*mp.exp(-25)
                       + mp.mpf(25928)/3*mp.exp(-10), 30),
                   "sqrt_N_over_required_bound_at_logN_24":
                       mp.nstr(mp.exp(12)/(216*28), 30),
                   "mid_b_right_endpoint_bound_at_logN_24":
                       mp.nstr(mp.exp(24*(1-2*L))/12, 30)}}
    print(json.dumps(results, indent=2), flush=True)
    rows = []
    for exponent in ((1, 10, 100) if args.quick else
                     (1, 2, 4, 10, 30, 100, 300, 1000, 3000, 10000)):
        n = mp.power(10, exponent)
        ell = mp.log(n)
        b = B*ell+d0
        m, dm = centered_correction(n, b)
        normalized_m = m*mp.power(n, I)*mp.sqrt(ell)
        normalized_dm = dm*mp.power(n, I)*mp.sqrt(ell)
        row = {"log10_N": exponent,
               "b_hat": mp.nstr(b, 30),
               "scaled_correction": mp.nstr(normalized_m, 30),
               "scaled_correction_target_D": mp.nstr(D, 30),
               "scaled_derivative": mp.nstr(normalized_dm, 30),
               "scaled_derivative_target":
                   mp.nstr(-mp.log(2*B)*D, 30)}
        rows.append(row)
        print(json.dumps(row), flush=True)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    (args.output_dir/"late_euler_diagnostics.json").write_text(
        json.dumps({**results, "rows": rows}, indent=2)+"\n")
    with (args.output_dir/"late_euler_diagnostics.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    if args.optimizers:
        optimizer_rows = []
        for integer_n in (2, 10, 100, 10000, 1000000000000):
            n = mp.mpf(integer_n)
            bhat = B*mp.log(n)+d0

            def derivative(b):
                _, dm = centered_correction(n, b)
                return n**p*(-mp.log(2)*2**(-b)
                    + n*mp.log(3)*3**(-b)
                    + n*mp.log(4)*4**(-b) + dm)

            optimum = mp.findroot(derivative, (bhat-mp.mpf("0.7"), bhat),
                                  solver="secant", tol=mp.mpf("1e-35"))
            m, _ = centered_correction(n, optimum)
            excess = 2**(-optimum)-n*3**(-optimum)-n*4**(-optimum)+m
            row = {"N": integer_n, "b_axis_maximum": mp.nstr(optimum, 35),
                   "axis_maximum_minus_one": mp.nstr(excess, 35),
                   "scaled_axis_excess": mp.nstr(n**p*excess, 35),
                   "b_hat_minus_b_axis_maximum": mp.nstr(bhat-optimum, 35)}
            optimizer_rows.append(row)
            print(json.dumps(row), flush=True)
        (args.output_dir/"late_euler_optimizers.json").write_text(
            json.dumps({"status": "numerical diagnostics, not interval certificates",
                        "rows": optimizer_rows}, indent=2)+"\n")
        with (args.output_dir/"late_euler_optimizers.csv").open("w", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=list(optimizer_rows[0]))
            writer.writeheader()
            writer.writerows(optimizer_rows)


if __name__ == "__main__":
    main()
