#!/usr/bin/env python3
"""Replay exact reconstruction identities and independent tail diagnostics.

Dependencies: Python >= 3.10, sympy, mpmath. No network or source archives.
Run from any directory. Results are written beside this script.

The all-order proof is in article.tex, Sections 2--4. Finite exact checks
and high-precision asymptotic diagnostics supplement, not replace, it.
"""
from __future__ import annotations

import argparse
from functools import lru_cache
import json
from pathlib import Path
import platform

import mpmath as mp
import sympy as sp

HERE = Path(__file__).resolve().parent
x, y = sp.symbols("x y")
fac = sp.factorial
HALF = sp.Rational(1, 2)


@lru_cache(None)
def mu(n):
    return sp.bernoulli(2*n) / fac(2*n)


@lru_cache(None)
def pi(n):
    return sp.Poly(sum(
        2*fac(2*n+2*t+1)*fac(2*n+1)
        / (fac(4*n+2)*fac(2*n-2*t+1)*fac(2*t))*x**t
        for t in range(n+1)), x)


def c(n):
    return (2*n+1)*fac(2*n+2)/fac(4*n+2)


def h(n):
    return fac(2*n+1)**2/(fac(4*n+2)*fac(4*n+3))


@lru_cache(None)
def orthogonal(n):
    if n == 0:
        return sp.Poly(1, x)
    return pi(n) - c(n)/c(n-1)*pi(n-1)


def norm(n):
    return sp.S.One if n == 0 else -c(n)/c(n-1)*h(n-1)


def functional(poly):
    return sum(value*mu(exponent) for (exponent,), value in sp.Poly(poly, x).terms())


def source_matrix(b):
    """Original binomial rule, independently of the factored Hankel form.

    Both binomial summands are omitted unless 2 <= lower <= upper.
    This includes the exceptional zeroth column correctly.
    """
    def entry(t, k):
        j = b+t
        result = sp.S.Zero
        for upper, lower in [(2*j-2*b+2, 2-2*k), (2*j, 2*b-2*k)]:
            if 2 <= lower <= upper:
                result += sp.binomial(upper, lower)/upper
        return sp.bernoulli(2*j-2*b+2*k)*result
    return sp.Matrix(b, b, entry)


def factored_matrix(b):
    return sp.Matrix(b, b, lambda t, k:
        fac(2*b+2*t-1)/fac(2*b-2*k)*mu(t+k)
        + (sp.Rational(2*t+1, 2)*sp.bernoulli(2*t) if k == 0 else 0))


@lru_cache(None)
def kernel(b):
    coeff = sp.Matrix(b, b, lambda n, t: orthogonal(n).nth(t))
    return coeff.T*sp.diag(*[1/norm(n) for n in range(b)])*coeff


@lru_cache(None)
def inverse_kernel(b):
    K = kernel(b)
    u = sp.Matrix([mu(t)*fac(2*b)*fac(2*t+1)/(2*fac(2*b+2*t-1)) for t in range(b)])
    v = K*u
    delta = 2-sp.bernoulli(2*b-2)
    J = K-v*K[0, :]/delta
    return sp.diag(*[fac(2*b-2*k) for k in range(b)])*J*sp.diag(
        *[1/fac(2*b+2*t-1) for t in range(b)])


def filter_poly(b, k):
    inverse = inverse_kernel(b)
    S = sum(inverse[k, t]*y**(2*b+2*t+1) for t in range(b))
    return sp.Poly(sp.expand(S.subs(y, x+HALF)-S.subs(y, x-HALF)), x)


@lru_cache(None)
def tail_coefficient(p, j):
    if j == 0:
        return sp.S.One/(p-1)
    return sp.bernoulli(2*j, HALF)*sp.rf(p, 2*j-1)/fac(2*j)


@lru_cache(None)
def product_coefficient(b, j):
    return sum(tail_coefficient(2, i)*tail_coefficient(2*b, j-i) for i in range(j+1))


def subtraction(b, W):
    R = sp.S.Zero
    for (exponent,), value in W.terms():
        for j in range(max(0, (exponent-2*b)//2+1)):
            R += value*product_coefficient(b, j)*x**(exponent-2*b-2*j)
    return sp.Poly(R, x)


def as_mp(value):
    numerator, denominator = sp.fraction(value)
    return mp.mpf(int(numerator))/int(denominator)


def evaluate_poly(poly, value):
    return mp.polyval([as_mp(a) for a in poly.all_coeffs()], value)


def numeric_series(b, k, cutoff, terms):
    """Direct Hurwitz tails, with an independently summed asymptotic tail.

    No target zeta value or late-coordinate formula enters this evaluator.
    The finite asymptotic continuation is a diagnostic, not an interval bound.
    """
    W = filter_poly(b, k)
    R = subtraction(b, W)
    total = mp.fsum(evaluate_poly(W, mp.mpf(n)+mp.mpf('0.5'))
                   *mp.zeta(2, n+1)*mp.zeta(2*b, n+1)
                   -evaluate_poly(R, mp.mpf(n)+mp.mpf('0.5'))
                   for n in range(cutoff))
    corrections = []
    for (exponent,), value in W.terms():
        for j in range(max(0, (exponent-2*b)//2+1), terms):
            power = 2*b+2*j-exponent
            corrections.append(as_mp(value*product_coefficient(b, j))
                               *mp.zeta(power, mp.mpf(cutoff)+mp.mpf('0.5')))
    return total+mp.fsum(corrections)


def exact_checks(max_b):
    checks = []
    for n in range(max_b):
        assert functional(pi(n)) == c(n)
        assert all(functional(x**j*pi(n).as_expr()) == 0 for j in range(1, n+1))
        assert functional(x**(n+1)*pi(n).as_expr()) == h(n)
        assert functional(orthogonal(n).as_expr()**2) == norm(n)
        checks.append(f"shifted_and_unshifted_functionals_n{n}")
    for b in range(2, max_b+1):
        H = sp.Matrix(b, b, lambda t, k: mu(t+k))
        K = kernel(b)
        assert K*H == sp.eye(b)
        assert all(K[0, t] == pi(b-1).nth(t)/c(b-1) for t in range(b))
        original = source_matrix(b)
        assert original == factored_matrix(b)
        inverse = inverse_kernel(b)
        assert inverse*original == sp.eye(b)
        assert original*inverse == sp.eye(b)
        assert all(inverse[0, t] == 2*sp.binomial(2*b-1, 2*t)
                   /((2*b-1)*(2-sp.bernoulli(2*b-2))) for t in range(b))
        checks.append(f"two_sided_inverse_original_binomial_matrix_b{b}")
    assert source_matrix(2) == sp.Matrix([[sp.Rational(3, 4), sp.Rational(1, 4)],
                                        [sp.Rational(2, 3), -sp.Rational(1, 12)]])
    P = 4032*x**6+2480*x**4-524*x**2-23
    assert filter_poly(2, 1).as_expr() == -3*P/528
    assert subtraction(2, filter_poly(2, 1)).as_expr() == -64*(63*x**2+2)/528
    t = 2*x
    P3 = 2145*t**10+40725*t**8+162302*t**6+146110*t**4+22161*t**2+61
    Q3 = 137280*t**4+1874240*t**2+1263872
    assert sp.expand(19520*filter_poly(3, 2).as_expr()+5*P3) == 0
    assert sp.expand(19520*subtraction(3, filter_poly(3, 2)).as_expr()+Q3) == 0
    checks.extend(["printed_zeta2_identity", "printed_zeta4_identity"])
    # A separate finite double-sum proof of every tested power-series coefficient.
    Zp, Zq = sp.symbols("Zp Zq")
    for p, q in [(2, 4), (2, 6), (3, 5)]:
        for n in range(1, 13):
            lhs = (Zp-sp.harmonic(n, p))*(Zq-sp.harmonic(n, q))
            rhs = Zp*Zq
            for j in range(1, n+1):
                rhs += (-Zq/sp.Integer(j)**p-Zp/sp.Integer(j)**q
                        +sp.harmonic(j-1, q)/sp.Integer(j)**p
                        +sp.harmonic(j-1, p)/sp.Integer(j)**q
                        +sp.S.One/sp.Integer(j)**(p+q))
            assert sp.expand(lhs-rhs) == 0
    checks.append("36_independent_tail_polylog_coefficients")
    return {"all_passed": True, "max_b": max_b, "check_groups": checks}


def write_coefficient_tables():
    rows = []
    readable = ["Exact even-zeta extraction rows", "", "x=n+1/2; A_p=Hurwitz zeta(p,n+1).",
                "For each row: sum_n [W(x) A_2 A_(2b) - R(x)] = multiplier*zeta(2k).", ""]
    for b in range(2, 7):
        for k in range(b):
            W = filter_poly(b, k)
            R = subtraction(b, W)
            den = sp.ilcm(*[v.q for v in W.all_coeffs()+R.all_coeffs()])
            Wi, Ri = sp.Poly(den*W.as_expr(), x), sp.Poly(den*R.as_expr(), x)
            rows.append({"b": b, "k": k, "multiplier": str(den),
                         "W_integer": str(Wi.as_expr()), "R_integer": str(Ri.as_expr()),
                         "inverse_row": [str(v) for v in inverse_kernel(b)[k, :]],
                         "W_coefficients_ascending": [str(Wi.nth(e)) for e in range(Wi.degree()+1)],
                         "R_coefficients_ascending": [str(Ri.nth(e)) for e in range(Ri.degree()+1)]})
            readable += [f"b={b}, k={k}, multiplier={den}", f"W(x) = {Wi.as_expr()}",
                         f"R(x) = {Ri.as_expr()}", ""]
    (HERE/"reconstruction_coefficients.json").write_text(json.dumps(rows, indent=2)+"\n")
    (HERE/"reconstruction_coefficients.txt").write_text("\n".join(readable))
    return len(rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-b", type=int, default=15)
    parser.add_argument("--skip-numerical", action="store_true")
    args = parser.parse_args()
    report = {"python": platform.python_version(), "sympy": sp.__version__,
              "mpmath": mp.__version__, "exact": exact_checks(args.max_b)}
    report["coefficient_rows"] = write_coefficient_tables()
    if not args.skip_numerical:
        mp.mp.dps = 110
        report["numerical"] = {"dps": mp.mp.dps, "interval_certificates": False, "rows": []}
        for b, k in [(2, 0), (2, 1), (3, 1), (3, 2), (4, 3), (6, 5)]:
            expected = mp.zeta(2*k)
            first = numeric_series(b, k, 160, 32)
            second = numeric_series(b, k, 320, 36)
            error = abs(second-expected)
            assert error < mp.mpf('1e-55')
            report["numerical"]["rows"].append({"b": b, "k": k,
                "expected": mp.nstr(expected, 80), "residual_160_32": mp.nstr(abs(first-expected), 12),
                "residual_320_36": mp.nstr(error, 12),
                "successive_difference": mp.nstr(abs(first-second), 12)})
    (HERE/"reconstruction_checks.json").write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
