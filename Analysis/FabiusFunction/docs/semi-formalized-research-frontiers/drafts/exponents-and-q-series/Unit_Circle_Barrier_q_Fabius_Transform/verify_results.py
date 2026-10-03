#!/usr/bin/env python3
"""Independent exact and high-precision checks for q_fabius_boundary.tex.

Run: python verify_results.py
Requires Python 3.10+, sympy, mpmath. No network access is used.
These finite checks supplement, and do not replace, the proofs in the article.
ed. (2026-09-30): the results go to rerun/verification_results.json unless
--output is given (the recorded verification_results.json is not overwritten
by default), and the JSON file is written with LF line endings on every
platform.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from math import factorial, gcd, lcm
from pathlib import Path
import json
import platform
import sys

try:
    import sympy as sp
    import mpmath as mp
except ImportError as exc:
    raise SystemExit("Install dependencies with: python -m pip install sympy mpmath") from exc

ROOT = Path(__file__).resolve().parent
Q = sp.Symbol('q')


def rational_coefficients(max_n: int) -> list[sp.Expr]:
    """Coefficients of A(q,z), obtained from its functional equation."""
    a = [sp.Integer(1)]
    for n in range(1, max_n + 1):
        value = sum((1-Q)**k * Q**(n-k) * a[n-k] / sp.factorial(k+1)
                    for k in range(1, n+1)) / (1-Q**n)
        a.append(sp.factor(sp.cancel(value)))
    return a


def reduction_mod_cyclotomic(value: sp.Expr, order: int) -> sp.Expr:
    """Evaluate a rational expression in Q modulo Phi_order(Q), exactly."""
    num, den = sp.fraction(sp.cancel(value))
    phi = sp.Poly(sp.cyclotomic_poly(order, Q), Q, domain=sp.QQ)
    n = sp.Poly(num, Q, domain=sp.QQ).rem(phi)
    d = sp.Poly(den, Q, domain=sp.QQ).rem(phi)
    if d.is_zero:
        raise ArithmeticError(f"Expression still has a pole at order {order}")
    return (n * sp.invert(d, phi)).rem(phi).as_expr()


def exact_checks(max_n: int = 12) -> dict:
    a = rational_coefficients(max_n)
    residue_cases = 0
    denominator_cases = 0
    for n, an in enumerate(a):
        assert sp.cancel(an.subs(Q, 0) - sp.Rational(1, factorial(n+1))) == 0
        assert sp.cancel(an.subs(Q, 1) - sp.Rational(1, 2**n * factorial(n))) == 0
        if n:
            cumulant_rhs = a[n-1]/2 + sum(
                sp.bernoulli(j)/sp.factorial(j) * (1-Q)**j/(1-Q**j)*a[n-j]
                for j in range(2, n+1, 2))
            assert sp.cancel(n*an-cumulant_rhs) == 0
        if n >= 2:
            D = sp.prod(sp.cyclotomic_poly(d, Q)**(n//lcm(2,d))
                        for d in range(2, n+1))
            assert sp.fraction(sp.cancel(D*an))[1].is_number
            reduced_den = sp.Poly(sp.denom(sp.cancel(an)), Q).monic()
            assert reduced_den == sp.Poly(D, Q).monic()
            denominator_cases += 1
        for ell in range(2, n+1):
            L = lcm(2, ell)
            k, r = divmod(n, L)
            if k == 0:
                continue
            # Clearing by 1-q^L, rather than q-zeta, permits exact cyclotomic arithmetic.
            value = sp.cancel((1-Q**L)**k * an)
            leading = (sp.bernoulli(L)*(1-Q)**L/(L*sp.factorial(L)))**k
            leading *= a[r]/sp.factorial(k)
            assert reduction_mod_cyclotomic(value-leading, ell) == 0
            if r in (0,1):
                assert reduction_mod_cyclotomic(value, ell) != 0
            residue_cases += 1
    return {
        'maximum_moment_degree': max_n,
        'functional_and_cumulant_recurrences_agree': True,
        'q_zero_and_q_one_specializations_pass': True,
        'cyclotomic_denominator_cases': denominator_cases,
        'minimal_denominator_equals_upper_divisor_through_tested_degree': True,
        'cyclotomic_leading_coefficient_cases': residue_cases,
        'first_coefficients': [str(x) for x in a[:7]],
        'denominators': {str(n): str(sp.factor(sp.denom(a[n])))
                         for n in range(2, max_n+1)},
    }


def valuation(base: int, n: int) -> int:
    if base < 2 or n == 0:
        raise ValueError('valuation requires base >= 2 and n != 0')
    n, answer = abs(n), 0
    while n % base == 0:
        n //= base
        answer += 1
    return answer


def multiplicity_checks() -> dict:
    cases = 0
    for numerator, denominator, r in [(2,1,1),(3,2,1),(3,2,2),(-2,1,2),(-5,3,3)]:
        rho = Fraction(numerator, denominator)
        for j in range(9):
            for k in range(1, 41):
                right = valuation(abs(numerator), k)
                left = j//r if denominator == 1 else min(j//r, valuation(denominator,k))
                expected = 1 + left + right
                # An exact count in each rotational residue class; larger j' give |k'|<1.
                actual = 0
                for jp in range(j % r, j + r*(right+3) + 1, r):
                    exponent = (j-jp)//r
                    kp = Fraction(k) * rho**exponent
                    if kp.denominator == 1:
                        actual += 1
                assert actual == expected
                cases += 1
    return {'exact_collision_counts': cases, 'all_pass': True}


def c(n: int) -> mp.mpf:
    return mp.bernoulli(n)/(n*mp.factorial(n))


def log_A(q: mp.mpc, z: mp.mpc, terms: int = 150) -> mp.mpc:
    """The analytic logarithm from the convergent cumulant series.

    Error decreases geometrically when |(1-q)z| < 2*pi. This routine is a
    high-precision check, not an interval-arithmetic certification.
    """
    w = (1-q)*z
    if abs(q) >= 1 or abs(w) >= 2*mp.pi:
        raise ValueError('log_A requires |q|<1 and |(1-q)z|<2*pi')
    return z/2 + mp.fsum(c(n)*w**n/(1-q**n) for n in range(2, 2*terms+1, 2))


def cusp_data(ell: int, z: mp.mpc, terms: int = 150) -> tuple:
    xi = mp.exp(2j*mp.pi/ell)
    w = (1-xi)*z
    L = lcm(2,ell)
    C = mp.fsum(c(n)*w**n/n for n in range(L, L*terms+1, L))
    Cp = mp.fsum(c(n)*w**(n-1) for n in range(L, L*terms+1, L))
    F0 = mp.fsum(c(n)*w**n*(mp.mpf('0.5') if n % ell == 0
                           else 1/(1-xi**n))
                  for n in range(2,2*terms+1,2))
    D = z/2 + xi*z*Cp + F0
    v = (1j*w/(2*mp.pi))**L
    C_zeta = -mp.mpf(2)/L**2 * mp.fsum(mp.zeta(k*L)*v**k/k**2
                                      for k in range(1,terms+1))
    assert abs(C-C_zeta) < mp.mpf('1e-65')
    lower = mp.mpf(2)*mp.zeta(L)/L**2*abs(v)*(2-mp.pi**2/6)
    assert abs(C) >= lower
    return xi, C, D


def fmt(z: mp.mpc, digits: int = 24) -> str:
    return mp.nstr(z, digits)


def numeric_checks() -> dict:
    mp.mp.dps = 85
    cusp_rows = []
    for ell in [2,3,4,5,6,8]:
        xi, C, D = cusp_data(ell, mp.mpc(1))
        errors = []
        for ts in ['0.04','0.02','0.01','0.005']:
            t = mp.mpf(ts)
            logv = log_A(xi*mp.exp(-t), mp.mpc(1))
            e0 = abs(t*logv-C)
            e1 = abs(logv-C/t-D)
            errors.append(e1)
            cusp_rows.append({'order':ell,'t':ts,'C':fmt(C),'D':fmt(D),
                              'abs_t_logA_minus_C':fmt(e0),
                              'abs_logA_minus_C_over_t_minus_D':fmt(e1)})
        # This is a loose finite consistency check of the claimed O(t) remainder.
        assert errors[-1] < errors[0]
    zero_rows = []
    z = mp.mpf(10)
    eta = mp.exp(2j*mp.pi/3)
    target = 2j*mp.pi/z
    for j in [20,40,80,160,320]:
        u0 = mp.log(target/((1-eta)*eta**j))
        def f(u: mp.mpc) -> mp.mpc:
            return eta**j*mp.exp(u)*(1-eta*mp.exp(u/j))-target
        u = mp.findroot(f, (u0,u0+mp.mpf('0.001')), tol=mp.mpf('1e-75'))
        qj = eta*mp.exp(u/j)
        residual = abs((1-qj)*qj**j*z-2j*mp.pi)
        assert abs(qj) < 1
        assert residual < mp.mpf('1e-70')
        zero_rows.append({'j':j,'q':fmt(qj),'abs_q':fmt(abs(qj)),
                          'distance_to_eta':fmt(abs(qj-eta)),
                          'residual':fmt(residual)})
    return {'precision_decimal_digits':mp.mp.dps,'cusp_rows':cusp_rows,
            'zero_condensation_rows':zero_rows}


def main() -> None:
    # ed. (2026-09-30): output option; the default leaves the recorded file untouched.
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=ROOT/'rerun'/'verification_results.json',
                        help='JSON output file (default: rerun/verification_results.json; '
                             'pass verification_results.json to overwrite the recorded file)')
    args = parser.parse_args()
    result = {'environment': {'python':platform.python_version(),
                              'sympy':sp.__version__, 'mpmath':mp.__version__}}
    print('Checking exact moment algebra...', flush=True)
    result['moments'] = exact_checks()
    print('Checking exact pole collisions...', flush=True)
    result['divisors'] = multiplicity_checks()
    print('Checking numerical cusp asymptotics and zero condensation...', flush=True)
    result['numerics'] = numeric_checks()
    result['status'] = 'PASS'
    # ed. (2026-09-30): configurable path; newline='\n' so the JSON is LF on Windows too.
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n', newline='\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'numerics'}, indent=2))
    print(f'PASS: full numerical results saved to {args.output.name}')

if __name__ == '__main__':
    main()
