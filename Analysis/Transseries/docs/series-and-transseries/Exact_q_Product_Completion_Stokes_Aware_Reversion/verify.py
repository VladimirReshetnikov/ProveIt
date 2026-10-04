#!/usr/bin/env python3
"""Reproduce checks for Exact q-Product Completion and Stokes-Aware Reversion.

The completion check evaluates the product and the Borel median independently.
Fold checks then use L0 = log(q-gamma) - completion. These are floating-point
experiments, not interval enclosures or formal proofs. All constants are
computed at the active mpmath precision; no machine-precision float inputs
are used in the research tests.

Usage: python verify.py --dps 150 --output verification_results.json
Dependencies: mpmath, sympy. Tested with mpmath 1.3.0 and sympy 1.14.0.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Callable

import mpmath as mp
import sympy as sp


def action() -> Any:
    return 4 * mp.pi**2


def tolerance() -> Any:
    return mp.power(10, -(mp.mp.dps - 12))


def fmt(value: Any, digits: int = 35) -> str:
    return mp.nstr(value, digits)


def log_product(a: Any, t: Any) -> Any:
    """Log(e^(-a*t);e^(-t))_infinity using its defining logarithmic series."""
    if mp.re(t) <= 0 or mp.re(a * t) <= 0:
        raise ValueError("The defining series requires Re(t)>0 and Re(a*t)>0.")
    total = mp.mpc(0)
    for n in range(1, 100_000):
        term = -mp.exp(-a * n * t) / (n * (-mp.expm1(-n * t)))
        total += term
        if abs(term) < tolerance():
            return total
    raise ArithmeticError("Product series exceeded its iteration limit.")


def core(a: Any, t: Any) -> Any:
    return (-mp.pi**2 / (6 * t) + (mp.mpf('0.5') - a) * mp.log(t)
            + mp.log(2 * mp.pi) / 2 - mp.loggamma(a)
            + mp.bernpoly(2, a) * t / 4)


def coefficient(a: Any, j: int) -> Any:
    return (-mp.bernoulli(2 * j) * mp.bernpoly(2 * j + 1, a)
            / (2 * j * mp.factorial(2 * j + 1)))


def dual(a: Any, t: Any, sign: int = 0) -> Any:
    """Dual D^0, D^+, or D^-; sign must be 0, +1, or -1."""
    if sign not in (-1, 0, 1):
        raise ValueError("Invalid lateral sign.")
    q = mp.exp(-action() / t)
    ratio = abs(q) * mp.exp(2 * mp.pi * abs(mp.im(a)))
    if ratio >= 1:
        raise ValueError("Dual logarithmic series is outside its convergence disk.")
    total = mp.mpc(0)
    for k in range(1, 100_000):
        phase = (mp.cos(2 * mp.pi * k * a) if sign == 0
                 else mp.exp(sign * 2j * mp.pi * k * a))
        total -= phase * q**k / (k * (1 - q**k))
        if ratio**k < tolerance():
            return total
    raise ArithmeticError("Dual series exceeded its iteration limit.")


def kernel(x: Any) -> Any:
    """Principal-value kernel, with continuation from positive real x."""
    if mp.re(x) <= 0:
        raise ValueError("This verification uses only Re(x)>0.")
    return -(mp.exp(-x) * mp.ei(x) - mp.exp(x) * mp.e1(x)) / mp.pi


def borel_median(a: Any, t: Any, cutoff: int, subtract: int) -> Any:
    """Independent accelerated PV evaluation; valid for real 0<a<1.

    Returns a truncated accelerated infinite sum, not a certified enclosure.
    """
    if mp.im(a) != 0 or not (0 < a < 1):
        raise ValueError("The Fourier-kernel test requires real 0<a<1.")
    total = sum(coefficient(a, j) * t**(2 * j)
                for j in range(1, subtract + 1))
    for n in range(1, cutoff + 1):
        b = sum(mp.sin(2 * mp.pi * d * a) / d
                for d in range(1, n + 1) if n % d == 0)
        x = action() * n / t
        partial = -2 / mp.pi * sum(mp.factorial(2 * j - 1) / x**(2 * j)
                                   for j in range(1, subtract + 1))
        total += b * (kernel(x) - partial)
    return total


def log_qgamma(a: Any, t: Any, derivative: int = 0) -> Any:
    """Exact logarithmic series or its convergent a-derivative series."""
    if derivative < 0:
        raise ValueError("Derivative order must be nonnegative.")
    if derivative == 0:
        return (log_product(1, t) - log_product(a, t)
                + (1 - a) * mp.log(-mp.expm1(-t)))
    if mp.re(t) <= 0 or mp.re(a * t) <= 0:
        raise ValueError("The derivative series is not convergent here.")
    total = mp.mpc(0)
    for n in range(1, 100_000):
        term = n**(derivative - 1) * mp.exp(-a * n * t) / (-mp.expm1(-n * t))
        total += term
        if abs(term) < tolerance():
            break
    else:
        raise ArithmeticError("q-gamma derivative series exceeded its limit.")
    correction = mp.log(-mp.expm1(-t)) if derivative == 1 else 0
    return (-t)**derivative * total - correction


def completion(a: Any, z: Any, derivative: int = 0) -> Any:
    """Exact q-gamma completion E(a,z), differentiated in a if requested."""
    if derivative < 0:
        raise ValueError("Derivative order must be nonnegative.")
    ratio = abs(z) * mp.exp(2 * mp.pi * abs(mp.im(a)))
    if ratio >= 1:
        raise ValueError("Completion is outside its logarithmic convergence disk.")
    total = mp.mpc(0)
    for k in range(1, 100_000):
        theta = 2 * mp.pi * k * a
        factor = (mp.cos(theta) - 1 if derivative == 0 else
                  (2 * mp.pi * k)**derivative
                  * mp.cos(theta + derivative * mp.pi / 2))
        total += factor * z**k / (k * (1 - z**k))
        if ratio**k < tolerance():
            return total
    raise ArithmeticError("Completion series exceeded its iteration limit.")


def newton(f: Callable[[Any], Any], df: Callable[[Any], Any], x: Any) -> Any:
    """High-precision local Newton solve with a displacement stopping test."""
    threshold = mp.power(10, -(mp.mp.dps - 40))
    for _ in range(40):
        slope = df(x)
        if slope == 0:
            raise ArithmeticError("Zero slope encountered in local Newton solve.")
        step = f(x) / slope
        x -= step
        if abs(step) < threshold:
            return x
    raise ArithmeticError("Local Newton solve did not converge.")


def symbolic_checks() -> dict[str, Any]:
    """Exact finite algebra checks; analytic theorems are not tested here."""
    a, z = sp.symbols('a z')
    # The local kernel sin((2a-1)z)/sin(z) with its constant removed.
    order = 6
    series = sp.series(sp.sin((2*a-1)*z) / sp.sin(z) - (2*a-1),
                       z, 0, 2*order+2).removeO().expand()
    count = 0
    for n in range(1, order+1):
        borel_coeff = series.coeff(z, 2*n) * sp.zeta(2*n) / (4*sp.pi)**(2*n)
        expected = (-sp.bernoulli(2*n)*sp.bernoulli(2*n+1, a)
                    / (2*n*sp.factorial(2*n+1)*sp.factorial(2*n-1)))
        assert sp.simplify(borel_coeff - expected) == 0
        count += 1
        ell = (sp.bernoulli(2*n)/(2*n*sp.factorial(2*n))
               * (sp.bernoulli(2*n+1, a)/(2*n+1)+1-a))
        increment = sp.bernoulli(2*n)*(a**(2*n)-1)/(2*n*sp.factorial(2*n))
        assert sp.simplify(ell.subs(a, a+1)-ell-increment) == 0
        count += 1
    c = [2, -9, 14, -9, 2]
    for bases in ([sp.Rational(1, 2)**j for j in range(5)],
                  [sp.Integer(2)**j for j in range(5)],
                  [sp.Integer(1)]*5, [sp.Integer(j) for j in range(5)]):
        assert sum(cj*b for cj, b in zip(c, bases)) == 0
        count += 1
    f, f2, AA, C1, C2 = sp.symbols('f f2 A C1 C2', nonzero=True)
    d1 = -C1/f
    d2 = -C2/f-AA*C1**2/f**2-f2*C1**2/(2*f**3)
    assert sp.simplify(f*d2+f2*d1**2/2-AA*C1*d1+C2) == 0
    count += 1
    kappa, ep, e2 = sp.symbols('kappa ep e2', nonzero=True)
    b1 = -ep/kappa
    assert sp.simplify(kappa*b1+ep) == 0
    assert sp.simplify(kappa*b1**2/2+ep*b1+e2-(e2-ep**2/(2*kappa))) == 0
    count += 2
    return {'passed_exact_assertions': count, 'borel_orders_checked': order,
            'scope': 'Finite symbolic identities only; not convergence or formal proof.'}


def identity_checks() -> list[dict[str, str]]:
    samples = [(mp.mpf(1)/3, mp.mpf('0.7')),
               (mp.mpf(2)/5, mp.mpf('1.2')),
               (mp.mpf(1)/3, mp.mpf('2')),
               (mp.mpf(1)/3, mp.mpc('0.8', '0.3')),
               (mp.mpf('0.5'), mp.mpf('1'))]
    results = []
    for a, t in samples:
        exact_remainder = log_product(a, t)-core(a, t)-dual(a, t)
        coarse = borel_median(a, t, 60, 10)
        refined = borel_median(a, t, 80, 12)
        error = abs(exact_remainder-coarse)
        refined_error = abs(exact_remainder-refined)
        assert error < mp.mpf('1e-42'), 'Independent completion discrepancy is too large.'
        q = mp.exp(-action()/t)
        residue_jump = mp.mpc(0)
        for n in range(1, 1000):
            b = sum(mp.sin(2*mp.pi*d*a)/d for d in range(1, n+1) if n % d == 0)
            residue_jump -= 2j*mp.pi*(b/mp.pi)*q**n
            if abs(q)**n < tolerance():
                break
        jump_error = abs(dual(a, t, 1)-dual(a, t, -1)-residue_jump)
        assert jump_error < mp.mpf('1e-80')
        results.append({'a': fmt(a), 't': fmt(t),
                        'coarse_discrepancy': fmt(error),
                        'refined_discrepancy': fmt(refined_error),
                        'refinement_change': fmt(abs(refined-coarse)),
                        'completion_size': fmt(abs(dual(a, t))),
                        'jump_series_discrepancy': fmt(jump_error)})
    return results


def fold_checks() -> list[dict[str, Any]]:
    results = []
    for ts in ['1.5', '1.0', '0.75']:
        t = mp.mpf(ts)
        z = mp.exp(-action()/t)
        L = lambda a, r=0: log_qgamma(a, t, r)
        # This group uses the proven completion to evaluate the carrier.
        H = lambda a, r=0: L(a, r)-completion(a, z, r)
        alpha0 = newton(lambda a: H(a, 1), lambda a: H(a, 2), mp.mpf('1.44'))
        alpha = newton(lambda a: L(a, 1), lambda a: L(a, 2), alpha0)
        kappa, k3 = H(alpha0, 2), H(alpha0, 3)
        e = mp.cos(2*mp.pi*alpha0)-1
        ep = -2*mp.pi*mp.sin(2*mp.pi*alpha0)
        e2 = e+(mp.cos(4*mp.pi*alpha0)-1)/2
        v0, v = H(alpha0), L(alpha)
        u0 = mp.sqrt(-2*e/kappa)
        u1 = -ep/kappa+k3*e/(3*kappa**2)
        roots, remainders = [], []
        for sign in [-1, 1]:
            approx = alpha0+sign*mp.sqrt(z)*u0+z*u1
            root = newton(lambda a: L(a)-v0, lambda a: L(a, 1), approx)
            roots.append(root)
            remainders.append((root-approx)/z**mp.mpf('1.5'))
        shift = (alpha-alpha0)/z
        predicted_shift = -ep/kappa
        value_residual = (v-v0-e*z-(e2-ep**2/(2*kappa))*z**2)/z**3
        assert abs(shift-predicted_shift) < mp.mpf('1e-7')
        assert abs(value_residual) < 2000
        assert max(abs(vv) for vv in remainders) < 1000
        gap = (roots[1]-roots[0])/mp.sqrt(z)
        assert abs(gap-2*u0) < mp.mpf('1e-8')
        results.append({'t': ts, 'Q': fmt(z), 'alpha0': fmt(alpha0),
                        'critical_shift_over_Q': fmt(shift),
                        'predicted_shift_over_Q': fmt(predicted_shift),
                        'critical_value_shift_over_Q': fmt((v-v0)/z),
                        'predicted_value_shift_over_Q': fmt(e),
                        'critical_value_remainder_over_Q3': fmt(value_residual),
                        'inverse_gap_over_sqrtQ': fmt(gap),
                        'predicted_inverse_gap_over_sqrtQ': fmt(2*u0),
                        'inverse_remainders_over_Q3half': [fmt(vv) for vv in remainders]})
    return results


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dps', type=int, default=150)
    parser.add_argument('--output', type=Path, default=Path('verification_results.json'))
    args = parser.parse_args()
    if args.dps < 100:
        parser.error('At least 100 decimal digits are required for these fold tests.')
    mp.mp.dps = args.dps
    print('Checking finite symbolic identities...', flush=True)
    symbolic = symbolic_checks()
    print('Evaluating independent product/Borel identities...', flush=True)
    identities = identity_checks()
    print('Checking completed critical points and inverse layers...', flush=True)
    folds = fold_checks()
    report = {'status': 'all checks passed', 'working_decimal_digits': args.dps,
              'mpmath_version': mp.__version__, 'sympy_version': sp.__version__,
              'qualification': ('Numerical results are high-precision experiments, '
                                'not interval-certified enclosures or formal proofs.'),
              'symbolic': symbolic, 'independent_completion': identities,
              'fold_using_exact_completion': folds}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(f'All checks passed. Output: {args.output}', flush=True)


if __name__ == '__main__':
    main()
