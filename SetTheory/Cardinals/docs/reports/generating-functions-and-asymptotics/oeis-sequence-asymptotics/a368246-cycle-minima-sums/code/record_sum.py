#!/usr/bin/env python3
"""Public finite computations for Report234 / OEIS A368246 (no network).

The certificate checks arithmetic consequences, not the analytic remainder theorem.
Newton results are roots of explicitly chosen finite models, never integer threshold
certificates. All computations terminate at the documented finite cutoffs.
"""
from __future__ import annotations
import argparse
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
from fractions import Fraction
from itertools import permutations
import json
from math import factorial
import os
from pathlib import Path
import sys

import mpmath as mp

if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(640)
ROOT = Path(__file__).resolve().parents[1]
MAX_EXACT_N = 200
MAX_DECIMAL_N = 6000


def require(condition, message):
    if not condition:
        raise ValueError(message)


def integer(value, lower, upper, label):
    require(isinstance(value, int) and not isinstance(value, bool), label + ' must be an integer')
    require(lower <= value <= upper, '%s must be in [%d, %d]' % (label, lower, upper))
    return value


def new_file_path(value):
    """Validate the raw spelling before normalizing; never reuse a destination."""
    require(bool(value), 'output path must be nonempty')
    require(not any(part in ('.', '..') for part in str(value).split(os.sep)),
            'output path must not contain dot or dot-dot components')
    out = Path(os.path.abspath(value))
    for path in (out, *out.parents):
        require(not path.is_symlink(), 'output path has a live or dangling symlink ancestor')
    require(not out.exists(), 'output file must be new')
    require(out != ROOT and ROOT not in out.parents, 'output must be outside the source package')
    require(out.parent.is_dir(), 'output parent must already exist')
    return out


def emit(data, output=None):
    encoded = json.dumps(data, indent=2, sort_keys=True, ensure_ascii=True) + '\n'
    if output is None:
        print(encoded, end='')
    else:
        path = new_file_path(output)
        with path.open('x', encoding='utf-8', newline='\n') as handle:
            handle.write(encoded)


def finite_counts(nmax=60):
    """Integer multiplication of prod_{k=1}^n (k-1+z^k), truncated at nmax.

    Every coefficient needed by the diagonals n <= nmax is retained exactly.
    This routine never obtains sequence coefficients from asymptotic fixtures.
    """
    integer(nmax, 0, MAX_EXACT_N, 'nmax')
    row = [1] + [0] * nmax
    diagonal = [1]
    for n in range(1, nmax + 1):
        new = [(n - 1) * value for value in row]
        for k in range(n, nmax + 1):
            new[k] += row[k - n]
        row = new
        diagonal.append(row[n])
    return diagonal


def rational_coefficients(nmax=60):
    """Independent Fraction multiplication of prod_{j>=1}(1+z^(j+1)/j).

    Return b_n, 1 <= n <= nmax, at indices n-1. Degree > nmax-1 is irrelevant.
    """
    integer(nmax, 1, MAX_EXACT_N, 'nmax')
    coeff = [Fraction(0)] * nmax
    coeff[0] = Fraction(1)
    for j in range(1, nmax - 1):
        for k in range(nmax - 1, j, -1):
            coeff[k] += coeff[k - j - 1] / j
    return coeff


def brute_counts(n):
    integer(n, 0, 8, 'brute n')
    records = cycles = 0
    for p in permutations(range(1, n + 1)):
        maximum = record_sum = 0
        for position, value in enumerate(p, 1):
            if value > maximum:
                maximum = value
                record_sum += position
        records += record_sum == n
        seen = set()
        minimum_sum = 0
        for start in range(1, n + 1):
            if start not in seen:
                cycle = []
                k = start
                while k not in seen:
                    seen.add(k)
                    cycle.append(k)
                    k = p[k - 1]
                minimum_sum += min(cycle)
        cycles += minimum_sum == n
    return {'n': n, 'records': records, 'cycle_minima': cycles}


def tree_log_coefficient(q, degree):
    """Exact [s^degree] B_q(s), using its finite rooted-tree coefficient sum."""
    integer(q, 1, 41, 'root order')
    integer(degree, 0, 40, 'jet degree')
    return sum((Fraction(r ** (r - 1) * (-r) ** (degree - r + 1),
                         factorial(r) * factorial(degree - r + 1))
                for r in range(q, degree + 2, q)), Fraction(0))


def gamma_root(q, root):
    integer(q, 2, 40, 'root order')
    # The exceptional roots +/-i must be treated after removing 1+z^2.
    require(abs(1 + root * root) > mp.mpf('1e-20'),
            'at +/-i use the nonzero quotient, not the unremoved Gamma product')
    return mp.fprod(mp.gamma(mp.mpf(r) / q) /
                    mp.gamma((r + root ** (r + 1)) / q) for r in range(1, q + 1))


def polylog_root_quotient(q, root, cutoff=115):
    """Approximate F(root)/(1+root^2), independently of Gamma products.

    The omitted logarithm has absolute value <= 3*2^(-cutoff)/(cutoff+1).
    This analytic truncation bound does not certify mpmath roundoff.
    """
    integer(q, 2, 40, 'root order')
    integer(cutoff, 10, 400, 'polylog cutoff')
    h = -root * mp.log(1 - root) - root * root
    for r in range(2, cutoff + 1):
        zr = root ** r
        li = mp.zeta(r) if r % q == 0 else mp.polylog(r, zr)
        h += (-1) ** (r + 1) * zr * (li - zr) / r
    return mp.exp(h)


def amplitudes(digits=80, cutoff=115):
    integer(digits, 40, 200, 'digits')
    integer(cutoff, 10, 400, 'polylog cutoff')
    with mp.workdps(digits):
        omega = mp.exp(2j * mp.pi / 3)
        c = gamma_root(3, omega)
        cp = (1 + omega * omega) * polylog_root_quotient(3, omega, cutoff)
        qi = (mp.gamma(mp.mpf(5) / 4) * mp.gamma(mp.mpf(1) / 2) * mp.gamma(mp.mpf(3) / 4)
              / (mp.gamma((2 - 1j) / 4) * mp.gamma((4 + 1j) / 4)))
        qp = polylog_root_quotient(4, mp.mpc(0, 1), cutoff)
        tail = 3 * mp.power(2, -cutoff) / (cutoff + 1)
        return {'C_omega': c, 'C_omega_polylog': cp, 'Q_i': qi, 'Q_i_polylog': qp,
                'omitted_log_bound': tail,
                'C_omega_truncation_bound': abs(cp) * mp.expm1(tail),
                'Q_i_truncation_bound': abs(qp) * mp.expm1(tail)}


def model_values(x, order=3, c=None):
    """Return B_K(x), B_K'(x) for the expressly real K=2 or K=3 model."""
    require(order in (2, 3), 'model order must be 2 or 3')
    x = mp.mpf(x)
    require(mp.isfinite(x) and x > 2, 'model x must be finite and greater than 2')
    co, si = mp.cospi(x), mp.sinpi(x)
    b = mp.exp(-mp.euler) + co / x ** 2
    derivative = -mp.pi * si / x ** 2 - 2 * co / x ** 3
    if order == 3:
        if c is None:
            c = gamma_root(3, mp.exp(2j * mp.pi / 3))
        factor = 8 - 2 * mp.euler - 2 * mp.log(x)
        phase = mp.exp((2j * mp.pi / 3) * (1 - x))
        periodic = 6 * mp.re(c * phase)
        periodic_prime = 6 * mp.re(c * (-2j * mp.pi / 3) * phase)
        numerator = co * factor + periodic
        b += numerator / x ** 3
        derivative += (-mp.pi * si * factor - 2 * co / x + periodic_prime) / x ** 3
        derivative -= 3 * numerator / x ** 4
    return b, derivative



def finite_model_iterate(log_y, order=3, digits=80):
    """Exactly t_K undamped Newton steps, t_2=2 and t_3=3.

    This evaluates the article's finite construction. Its numerical arithmetic
    and asymptotic error constants are not certified. Invalid model values or
    nonpositive derivatives fail explicitly rather than invoking damping.
    """
    require(order in (2, 3), 'finite model order must be 2 or 3')
    integer(digits, 40, 200, 'digits')
    require(len(str(log_y)) <= 640, 'log-y input is limited to 640 characters')
    with mp.workdps(digits):
        target = mp.mpf(log_y)
        require(mp.isfinite(target) and 10 <= target <= mp.mpf('1e12'),
                'log-y must be finite and in [10, 1e12]')
        ell = target + mp.euler - mp.log(2 * mp.pi) / 2
        X = ell / mp.lambertw(ell / mp.e, 0)
        x = X + 1
        steps = 2 if order == 2 else 3
        c = gamma_root(3, mp.exp(2j * mp.pi / 3)) if order == 3 else None
        trace = []
        for iteration in range(steps + 1):
            b, bp = model_values(x, order, c)
            require(b > 0, 'undamped finite model is nonpositive at an iterate')
            residual = mp.loggamma(x) + mp.log(b) - target
            derivative = mp.digamma(x) + bp / b
            require(mp.isfinite(residual) and mp.isfinite(derivative) and derivative > 0,
                    'undamped finite model has invalid residual or derivative')
            trace.append({'iteration': iteration, 'x': mp.nstr(x, digits - 8),
                          'log_residual': mp.nstr(residual, 12)})
            if iteration < steps:
                x -= residual / derivative
                require(mp.isfinite(x) and x > 2, 'undamped iterate left the model domain')
        return {'order': order, 'prescribed_undamped_steps': steps,
                'model_iterate': mp.nstr(x, digits - 8),
                'log_residual': mp.nstr(residual, 12), 'iteration_history': trace,
                'status': 'FINITE_MODEL_ITERATE',
                'limitation': 'Exactly ceil(log2(K+2)) undamped steps; numerical evaluation, not a certified model root or integer sequence threshold.'}


def inverse_model(log_y, order=3, digits=80, max_steps=30):
    """Damped finite Newton evaluation of log Gamma(x)+log B_K(x)=log_y.

    No effective sequence remainder constant is supplied. The reported root,
    residual and adjacent integers therefore are not threshold certificates.
    """
    require(order in (2, 3), 'model order must be 2 or 3')
    integer(digits, 40, 200, 'digits')
    integer(max_steps, 1, 100, 'max_steps')
    require(len(str(log_y)) <= 640, 'log-y input is limited to 640 characters')
    with mp.workdps(digits):
        target = mp.mpf(log_y)
        require(mp.isfinite(target) and 10 <= target <= mp.mpf('1e12'),
                'log-y must be finite and in [10, 1e12]')
        ell = target + mp.euler - mp.log(2 * mp.pi) / 2
        X = ell / mp.lambertw(ell / mp.e, 0)
        x = X + 1
        starter = +x
        c = gamma_root(3, mp.exp(2j * mp.pi / 3)) if order == 3 else None
        tolerance = mp.power(10, -digits + 15)
        history = []
        converged = False
        for iteration in range(max_steps):
            b, bp = model_values(x, order, c)
            require(b > 0, 'finite model is nonpositive at an iterate')
            f = mp.loggamma(x) + mp.log(b) - target
            history.append({'iteration': iteration, 'x': mp.nstr(x, digits - 8),
                            'log_residual': mp.nstr(f, 12)})
            if abs(f) <= tolerance:
                converged = True
                break
            derivative = mp.digamma(x) + bp / b
            require(mp.isfinite(derivative) and derivative > 0, 'nonpositive model derivative')
            step = f / derivative
            accepted = False
            for _ in range(60):
                candidate = x - step
                if candidate > 2:
                    cb, _ = model_values(candidate, order, c)
                    if cb > 0:
                        cf = mp.loggamma(candidate) + mp.log(cb) - target
                        if abs(cf) < abs(f):
                            x = candidate
                            accepted = True
                            break
                step /= 2
            require(accepted, 'Newton damping did not produce an improving iterate')
        require(converged, 'finite Newton iteration did not converge within max_steps')
        return {'order': order, 'digits': digits, 'log_y': mp.nstr(target, digits - 8),
                'L': mp.nstr(ell, digits - 8), 'X': mp.nstr(X, digits - 8),
                'starter_X_plus_1': mp.nstr(starter, digits - 8),
                'model_root': mp.nstr(x, digits - 8),
                'log_residual': mp.nstr(f, 12), 'iterations': len(history) - 1,
                'iteration_history': history,
                'finite_order_construction': finite_model_iterate(log_y, order, digits),
                'status': 'CONVERGED_NUMERICAL_MODEL',
                'limitation': 'This is a finite-model numerical root, not a sequence threshold certificate; no certified mpmath roundoff or effective asymptotic remainder bound is asserted.'}


def decimal_coefficients(nmax=600, digits=60):
    """Directed Decimal enclosure of b_1,...,b_nmax, via nonnegative products.

    Division, multiplication and addition are all rounded down/up, respectively.
    These enclose exact finite coefficients, not the asymptotic remainder. No
    floating gamma/log/trigonometric evaluation inherits an interval guarantee.
    """
    integer(nmax, 1, MAX_DECIMAL_N, 'nmax')
    integer(digits, 20, 200, 'digits')
    arrays = []
    for rounding in (ROUND_FLOOR, ROUND_CEILING):
        with localcontext() as ctx:
            ctx.prec = digits
            ctx.rounding = rounding
            ctx.Emin = -999999
            ctx.Emax = 999999
            coeff = [Decimal(0)] * nmax
            coeff[0] = Decimal(1)
            for j in range(1, nmax - 1):
                reciprocal = Decimal(1) / Decimal(j)
                for k in range(nmax - 1, j, -1):
                    coeff[k] = coeff[k] + reciprocal * coeff[k - j - 1]
            require(all(value.is_finite() for value in coeff), 'nonfinite Decimal coefficient')
            arrays.append(coeff)
    return arrays[0], arrays[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    exact = sub.add_parser('exact', help='independent integer and rational coefficients')
    exact.add_argument('--n', type=int, default=60)
    exact.add_argument('--output')
    brute = sub.add_parser('brute', help='enumerate both permutation statistics through n <= 8')
    brute.add_argument('--n', type=int, default=8)
    brute.add_argument('--output')
    roots = sub.add_parser('roots', help='Gamma values, independent polylog evaluations and tail bounds')
    roots.add_argument('--digits', type=int, default=80)
    roots.add_argument('--cutoff', type=int, default=115)
    roots.add_argument('--output')
    inv = sub.add_parser('inverse', help='numerical root of finite K=2 or K=3 model; not a threshold certificate')
    inv.add_argument('--log-y', required=True)
    inv.add_argument('--order', type=int, choices=(2, 3), default=3)
    inv.add_argument('--digits', type=int, default=80)
    inv.add_argument('--max-steps', type=int, default=30)
    inv.add_argument('--output')
    dec = sub.add_parser('decimal', help='optional directed-rounding finite-coefficient diagnostic')
    dec.add_argument('--n', type=int, default=600)
    dec.add_argument('--digits', type=int, default=60)
    dec.add_argument('--output')
    args = parser.parse_args()
    # Fail early on unsafe paths, before doing potentially expensive work.
    if args.output is not None:
        new_file_path(args.output)
    if args.command == 'exact':
        integer(args.n, 1, MAX_EXACT_N, 'n')
        values = finite_counts(args.n)
        rationals = rational_coefficients(args.n)
        require(all(rationals[n - 1] * factorial(n - 1) == values[n]
                    for n in range(1, args.n + 1)), 'independent coefficient disagreement')
        result = {'status': 'PASS', 'nmax': args.n, 'a_n': values,
                  'b_n_for_n_1_through_nmax': [str(v) for v in rationals]}
    elif args.command == 'brute':
        integer(args.n, 0, 8, 'brute n')
        values = finite_counts(args.n)
        result = {'statistics': [brute_counts(n) for n in range(args.n + 1)]}
        require(all(r['records'] == r['cycle_minima'] == values[r['n']]
                    for r in result['statistics']), 'brute-force disagreement')
        result['status'] = 'PASS'
    elif args.command == 'roots':
        vals = amplitudes(args.digits, args.cutoff)
        with mp.workdps(args.digits):
            result = {key: ({'real': mp.nstr(mp.re(v), args.digits - 10),
                             'imaginary': mp.nstr(mp.im(v), args.digits - 10)}
                            if mp.im(v) else mp.nstr(v, args.digits - 10))
                      for key, v in vals.items()}
        result.update(digits=args.digits, cutoff=args.cutoff,
                      limitation='Tail bounds are analytic truncation bounds only; mpmath roundoff is not certified.')
    elif args.command == 'inverse':
        result = inverse_model(args.log_y, args.order, args.digits, args.max_steps)
    else:
        lo, hi = decimal_coefficients(args.n, args.digits)
        nlist = sorted(set([1, min(60, args.n)] + list(range(max(1, args.n - 5), args.n + 1))))
        result = {'nmax': args.n, 'digits': args.digits,
                  'coefficient_intervals': [{'n': n, 'lower': str(lo[n - 1]),
                                             'upper': str(hi[n - 1])} for n in nlist],
                  'limitation': 'Directed Decimal bounds enclose finite product coefficients only, not an asymptotic remainder or integer inverse threshold.'}
    emit(result, args.output)


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, ArithmeticError) as exc:
        raise SystemExit(str(exc))
