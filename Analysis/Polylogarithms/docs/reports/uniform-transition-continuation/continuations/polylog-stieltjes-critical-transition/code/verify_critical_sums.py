"""Reproducible diagnostics for the two new Lerch-velocity consequences.

The proofs are analytic.  SymPy verifies universal polynomial identities;
mpmath evaluates independently defined coefficients and sharp partial sums.
Floating-point output is diagnostic and does not certify global zero counts.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp
import sympy as sp
from sympy.functions.combinatorial.numbers import stirling

HERE = Path(__file__).resolve().parent


def even_coefficients(count=4):
    w, u = sp.symbols("w u")
    base = sp.series(w**2 / (sp.exp(w) - 1 - w), w, 0, 2 * count).removeO()
    c = {}
    const = {}
    for j in range(1, count + 1):
        expanded = sp.series(((u + w) * base)**j, w, 0, 2 * j).removeO()
        c[j] = sp.factor((-1)**j * expanded.coeff(w, 2*j-1) / (2*j))
    for p in range(1, count + 1):
        const[p] = sp.factor(sum((-1)**(j+1) * sp.factorial(j) *
                                stirling(p, j, kind=2) * c[j]
                                for j in range(1, p+1)))
    assert sp.simplify(c[1] - (u / 3 - 1)) == 0
    assert sp.simplify(c[2] - (-2*u*u/135 + u/3 - sp.Rational(2, 3))) == 0
    assert sp.simplify(const[2] - (4*u*u/135 - u/3 + sp.Rational(1, 3))) == 0
    return {str(j): str(c[j]) for j in c}, {str(p): str(const[p]) for p in const}


def velocity_coefficients(a, nmax):
    """Use the exact quadratic recurrence, evaluated at high precision."""
    loga = mp.log(a)
    p = [mp.mpf(0), -loga]
    for n in range(1, nmax):
        convolution = mp.fsum(p[j] * p[n-j] for j in range(1, n))
        p.append(((n+1-n*loga)*p[n] + mp.mpf(n)/2*convolution)/(n+1))
    return [p[n] / a**n for n in range(nmax+1)]


def stirling_crosscheck(a, coeffs, nmax=60):
    """Independent unsigned-Stirling coefficient extraction."""
    row = [1]
    largest = mp.mpf(0)
    for n in range(1, nmax+1):
        new = [0]*(n+1)
        for k in range(1, n+1):
            new[k] = row[k-1] + (n-1)*(row[k] if k < len(row) else 0)
        row = new
        actual = mp.fsum(mp.mpf(row[n-j+1]) * (-mp.log(a))**j /
                         mp.factorial(j) for j in range(1, n+1))/a**n
        largest = max(largest, abs(actual-coeffs[n]) / max(mp.mpf('1e-100'), abs(actual)))
    assert largest < mp.mpf('1e-150')
    return mp.nstr(largest, 12)


def binomial_kernel(beta, n):
    return mp.gamma(n-beta)/(mp.gamma(-beta)*mp.gamma(n+1))


def odd_coefficients(u_value, chi_value, count=4):
    """Evaluate the baseline Lagrange formula independently of c1/c3."""
    w, u = sp.symbols("w u")
    odd = {}
    f = sp.series(2*(sp.exp(w)-1-w)/w**2, w, 0, 2*count).removeO()
    for j in range(count):
        m = 2*j+1
        left = sp.series(f**(-sp.Rational(m, 2)), w, 0, m).removeO()
        right = sum(sp.binomial(sp.Rational(m, 2), k)*(w/u)**k for k in range(m))
        coeff = sp.expand(left*right).coeff(w, m-1)
        quotient = sp.factor((-2*u)**j*coeff/m)
        odd[j] = chi_value * sp.lambdify(u, quotient, "mpmath")(u_value)
    return odd


def generic_subtraction(p, n, q, odd):
    regular, oscillating = mp.mpc(0), mp.mpc(0)
    for j in range(p):
        alpha = mp.mpf(j)+mp.mpf(1)/2
        for l in range(j+1, p+1):
            falling = mp.fprod(alpha-k for k in range(l))
            pref = -odd[j]*int(stirling(p, l, kind=2))*(-1)**l*falling
            regular += pref*mp.fsum((-1)**i*mp.binomial(l, i)*
                                    binomial_kernel(alpha-l+i-1, n)
                                    for i in range(l-j))
    for j in range(p-1):
        alpha = mp.mpf(j)+mp.mpf(1)/2
        for l in range(j+2, p+1):
            falling = mp.fprod(alpha-k for k in range(l))
            pref = -mp.conj(odd[j])*int(stirling(p, l, kind=2))*(-1)**l*falling
            for i in range(l-j-1):
                for h in range(l-j-1-i):
                    oscillating += pref*(-1)**(i+h)*mp.binomial(l, i)*q**h/(1-q)**(h+1)*\
                                   binomial_kernel(alpha-l+i+h, n)
    return regular + q**(-n)*oscillating


def complex_text(z, digits=30):
    return {"real": mp.nstr(mp.re(z), digits), "imag": mp.nstr(mp.im(z), digits)}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE.parent / "verification" / "critical_sums_diagnostics.json")
    args=parser.parse_args()
    mp.mp.dps = 240
    a = mp.mpf(2)
    theta = mp.findroot(lambda t: 1-t/mp.tan(t)+mp.log(t/mp.sin(t))-mp.log(a), (1, 1.3))
    realpart = 1-theta/mp.tan(theta)
    u = realpart + 1j*theta
    tau = mp.exp(u)
    chi = mp.sqrt(-2*u)
    c2 = u/3-1
    c3 = chi*(mp.mpf(1)/2-u/18-1/(4*u))
    c4 = -2*u*u/135+u/3-mp.mpf(2)/3
    cp2 = c2-2*c4
    q = mp.conj(tau)/tau
    v = velocity_coefficients(a, 600)
    error = stirling_crosscheck(a, v)
    rows = []
    s1 = mp.mpc(0)
    s2 = mp.mpc(0)
    for n in range(1, 601):
        term = v[n]*tau**n
        s1 += n*term
        s2 += n*n*term
        if n in (40, 100, 200, 400, 600):
            t1 = chi/2*binomial_kernel(-mp.mpf(3)/2, n)
            t2 = chi/4*binomial_kernel(-mp.mpf(5)/2, n)-3*c3/4*binomial_kernel(-mp.mpf(3)/2, n)
            e2 = mp.conj(chi)*q**(-n)/(4*(1-q))*binomial_kernel(-mp.mpf(3)/2, n)
            rows.append({
                "N": n,
                "first_finite_part_estimate": complex_text(s1-t1),
                "first_scaled_error": mp.nstr(mp.sqrt(n)*abs(s1-t1-c2), 20),
                "second_finite_part_estimate": complex_text(s2-t2-e2),
                "second_scaled_error": mp.nstr(mp.sqrt(n)*abs(s2-t2-e2-cp2), 20),
                "second_error_without_conjugate_subtraction": mp.nstr(abs(s2-t2-cp2), 20),
            })
    runs = []
    run_start = 100
    run_sign = mp.sign(v[100])
    for n in range(101, 601):
        this_sign = mp.sign(v[n])
        if this_sign != run_sign:
            runs.append({"start": run_start, "end": n-1, "sign": int(run_sign)})
            run_start, run_sign = n, this_sign
    runs.append({"start": run_start, "end": 600, "sign": int(run_sign)})
    evens, finite_constants = even_coefficients(4)
    odd = odd_coefficients(u, chi, 4)
    assert abs(odd[0]-chi) < mp.mpf('1e-220')
    assert abs(odd[1]-c3) < mp.mpf('1e-220')
    generic_rows = []
    u_symbol = sp.symbols("u")
    for power in (2, 3, 4):
        target = sp.lambdify(u_symbol, sp.sympify(finite_constants[str(power)]), "mpmath")(u)
        for cutoff in (100, 200, 400, 600):
            total = mp.fsum(n**power*v[n]*tau**n for n in range(1, cutoff+1))
            subtraction = generic_subtraction(power, cutoff, q, odd)
            generic_rows.append({"p": power, "N": cutoff,
                                 "finite_part_estimate": complex_text(total-subtraction),
                                 "sqrt_N_times_error": mp.nstr(mp.sqrt(cutoff)*abs(total-subtraction-target), 20)})
    data = {
        "status": "exact symbolic identities plus numerical diagnostics; analytic proof is in section fragment",
        "baseline_commit": "570b0567f311cf1890865065896be2665f469e4f",
        "precision_digits": mp.mp.dps,
        "A": 2,
        "theta": mp.nstr(theta, 50),
        "u_star": complex_text(u, 50),
        "C1": complex_text(c2, 50),
        "C2": complex_text(cp2, 50),
        "even_puiseux_polynomials": evens,
        "finite_constant_polynomials": finite_constants,
        "independent_coefficient_max_relative_error": error,
        "partial_sum_diagnostics": rows,
        "general_formula_diagnostics": generic_rows,
        "max_same_sign_run_in_100_to_600": max(r["end"]-r["start"]+1 for r in runs),
        "example_same_sign_triples": [r for r in runs if r["end"]-r["start"]+1 == 3][:8],
    }
    args.output.write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps(data, indent=2))


if __name__ == "__main__":
    main()
