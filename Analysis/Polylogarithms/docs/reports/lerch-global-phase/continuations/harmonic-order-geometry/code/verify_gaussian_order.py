#!/usr/bin/env python3
"""Exact arithmetic and independent numerical audits for the order-zero paper.

No numerical computation here is a premise in the analytic real-zero proof.
The exact mode requires only the Python standard library. The --numeric mode
also requires mpmath; its outputs are diagnostics, not interval certificates.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json


def add(a, b):
    n = max(len(a), len(b))
    return [(a[k] if k < len(a) else 0) + (b[k] if k < len(b) else 0)
            for k in range(n)]


def scale(a, c):
    return [c * x for x in a]


def mul(a, b, size=None):
    n = len(a) + len(b) - 1 if size is None else size
    out = [F(0)] * n
    for j, x in enumerate(a):
        for k, y in enumerate(b):
            if j + k < n:
                out[j + k] += x * y
    return out


def deriv(a):
    return [k * a[k] for k in range(1, len(a))] or [F(0)]


def invert(a, n):
    out = [1 / F(a[0])]
    for k in range(1, n):
        out.append(-sum(a[j] * out[k - j]
                        for j in range(1, min(k + 1, len(a)))) / a[0])
    return out


def kernel_polynomials(n):
    """K^(j)(t)=sqrt(y)/(1+y)^(j+1)*(P_j(y)*log(1+y)+Q_j(y))."""
    P, Q = [F(1)], [F(0)]
    rows = [(P, Q)]
    for j in range(n):
        linear = [-F(1), F(2 * j + 1)]
        Pnext = add(mul(linear, P), mul([0, -2, -2], deriv(P)))
        Qnext = add(add(mul(linear, Q), mul([0, -2, -2], deriv(Q))),
                    mul([0, -2], P))
        while len(Pnext) > 1 and Pnext[-1] == 0:
            Pnext.pop()
        while len(Qnext) > 1 and Qnext[-1] == 0:
            Qnext.pop()
        P, Q = Pnext, Qnext
        rows.append((P, Q))
    return rows


def exact_checks():
    order = 30
    rows = kernel_polynomials(order)
    # Independent formal Taylor arithmetic for generalized secant derivative.
    size = order + 1
    cos = [F(0)] * size
    for j in range(0, size, 2):
        cos[j] = F((-1) ** (j // 2), factorial(j))
    sec = invert(cos, size)
    logsec_prime = mul(deriv(sec), cos, size - 1)
    logsec = [F(0)] + [logsec_prime[j - 1] / j for j in range(1, size)]
    sec_alpha_derivative = mul(sec, logsec, size)
    values = []
    for j, (P, Q) in enumerate(rows):
        # Pair (rational coefficient, coefficient of log 2).
        factor = F((-1) ** (j + 1), 2 ** (j + 1))
        actual = (factor * sum(Q), factor * sum(P))
        m = j // 2
        E = sec[2 * m] * factorial(2 * m)
        if j % 2:
            expected = (F((-1) ** (m + 1) * (2 * m + 1), 2) * E, F(0))
        else:
            Ep = sec_alpha_derivative[j] * factorial(j)
            expected = (F((-1) ** m, 2) * Ep, -F((-1) ** m, 2) * E)
            if m:
                assert Ep >= E > 0
        assert actual == expected, (j, actual, expected)
        values.append({"argument": -j, "rational": str(actual[0]),
                       "log2_coefficient": str(actual[1])})
    # Kernel derivative and convexity polynomial identities.
    assert rows[2] == ([F(1), F(-6), F(1)], [F(0), F(8), F(-4)])
    bracket_after_log_bound = add(mul([0, 1], rows[2][0]), rows[2][1])
    assert bracket_after_log_bound == [0, 9, -10, 1]
    # Every comparison in the global derivative bound is rational once the
    # elementary bounds pi>3, pi^2<10, log2<3/4, G>8/9 have been inserted.
    assert F(10, 1) / (16 * F(8, 9)) == F(45, 64) < F(3, 4)
    a, b, mu = F(4, 3), F(14, 9), F(3, 4)
    assert a * a + 2 * a * b * mu + b * b * mu == F(181, 27)
    assert F(181, 108) < F(9, 4)
    # exp(3/4)>1+3/4+(3/4)^2/2>2 proves log2<3/4.
    assert 1 + F(3, 4) + F(3, 4) ** 2 / 2 > 2
    # Archimedes pi<22/7 implies pi^2<10.
    assert F(22, 7) ** 2 < 10
    # Root's independent complex right-half-plane bound.
    tail = F(7, 800)
    for n in range(2, 6):
        tail += sum(F(1, j) for j in range(1, n + 1)) / (2 * n + 1) ** 3
    assert tail == F(122481517493, 3993750684000)
    assert 27 * tail == F(122481517493, 147916692000) < F(5, 6)
    return {"status": "passed", "negative_integer_orders_checked": order + 1,
            "negative_values": values,
            "global_derivative_constant_squared": "181/27",
            "derivative_at_q_ge_2_squared_bound": "181/108",
            "comparison_lower_bound_c_squared": "9/4",
            "right_half_plane_normalized_tail_bound": str(27 * tail)}


def numeric_checks(dps, full=False, records=None):
    import mpmath as mp
    mp.mp.dps = dps
    c = mp.pi / 2
    polyrows = kernel_polynomials(8)

    def to_mp(x):
        return mp.mpf(x.numerator) / x.denominator

    def kernel_derivative(t, j):
        y = mp.exp(-2 * t)
        P, Q = polyrows[j]
        p = mp.polyval([to_mp(x) for x in reversed(P)], y)
        q = mp.polyval([to_mp(x) for x in reversed(Q)], y)
        return mp.exp(-t) * (p * mp.log1p(y) + q) / (1 + y) ** (j + 1)

    def L(x):
        # This expression is a real function of a real x.
        return mp.euler + mp.re(mp.digamma((1 + 1j * x) / 2))

    def moments(q, derivative=False):
        # Direct x-space Fourier moments. Suitable for modest q, including
        # complex q needed for an independent continuation check.
        def f(x):
            return mp.power(x, q) / mp.cosh(c * x)
        intervals = [0, 1, 4, 12, mp.inf]
        A = mp.quad(lambda x: f(x) * L(x), intervals)
        B = mp.quad(lambda x: f(x) * mp.tanh(c * x), intervals)
        if not derivative:
            return A, B
        Ap = mp.quad(lambda x: f(x) * L(x) * mp.log(x), intervals)
        Bp = mp.quad(lambda x: f(x) * mp.tanh(c * x) * mp.log(x), intervals)
        return A, B, Ap, Bp

    def ratio(q):
        # v=c*x; gamma normalization prevents overflow or missed high-q peaks.
        q = mp.mpf(q)
        lognorm = mp.loggamma(q + 1)
        def f(v):
            return mp.exp(q * mp.log(v) - v - lognorm)
        spread = 10 * mp.sqrt(q + 1)
        intervals = sorted(set([mp.mpf(0), mp.mpf(1), q / 2,
                                max(mp.mpf(1), q - spread), q,
                                q + spread, 2 * q + 20])) + [mp.inf]
        A = mp.quad(lambda v: f(v) * L(v / c) / (1 + mp.exp(-2 * v)), intervals)
        B = mp.quad(lambda v: f(v) * (1 - mp.exp(-2 * v)) /
                    (1 + mp.exp(-2 * v)) ** 2, intervals)
        return A / (c * B)

    def S_fourier(s):
        q = -s
        A, B = moments(q)
        return (mp.cos(c * q) * A - c * mp.sin(c * q) * B) / 2

    def S_derivative_mellin(s, j):
        # Independent continuation by j integrations by parts, no digamma.
        return (-1) ** (j + 1) / mp.gamma(s + j) * mp.quad(
            lambda t: t ** (s + j - 1) * kernel_derivative(t, j),
            [0, mp.mpf('.25'), 1, 4, mp.inf])

    if records is None:
        records = {"classification": "nonrigorous numerical diagnostics",
                   "working_decimal_digits": dps, "cross_checks": [],
                   "ratios": [], "roots": []}
    if records["working_decimal_digits"] != dps:
        raise ValueError('Resumed diagnostics must use the same precision.')
    samples = ([] if records['cross_checks'] else
               [mp.mpf('-.5'), mp.mpf('-1.5'), mp.mpc('-.75', '.4')])
    for s in samples:
        left, right = S_fourier(s), S_derivative_mellin(s, 2)
        err = abs(left - right)
        assert err < mp.mpf(10) ** (-min(dps // 2, 20))
        records["cross_checks"].append({"s": str(s), "fourier": str(left),
                                         "kernel_mellin": str(right),
                                         "absolute_discrepancy": str(err)})
    for q in ([] if records['ratios'] else [2, 3, 6, 10]):
        A, B, Ap, Bp = moments(q, True)
        R, Rp = A / (c * B), (Ap * B - A * Bp) / (c * B ** 2)
        assert 0 < Rp < mp.sqrt(mp.mpf(181) / 27) / q < c
        records["ratios"].append({"q": q, "R": str(R), "R_prime": str(Rp)})
    m_values = [1, 2, 3, 5, 10] + ([50, 500] if full else [])
    already_done = {record['m'] for record in records['roots']}
    for m in m_values:
        if m in already_done:
            continue
        N = 2 * m + 1
        lam = mp.log(mp.mpf(N) / mp.pi) + mp.euler
        eps0 = mp.atan(c / lam) / c
        D = lam ** 2 + c ** 2
        eps1 = eps0 - (mp.mpf('.5') - eps0) / (N * D)
        def equation(eps):
            return c / mp.tan(c * eps) - c * ratio(N - eps)
        # findroot is a diagnostic, not a certificate. The analytic theorem
        # independently establishes existence, uniqueness, and simplicity.
        eps = mp.findroot(equation, (max(mp.mpf('.01'), eps1 * mp.mpf('.95')),
                                      min(mp.mpf('.99'), eps1 * mp.mpf('1.05'))),
                          solver='secant', verify=True)
        assert 0 < eps < 1
        zero = -N + eps
        root = {"m": m, "zero": str(zero), "epsilon": str(eps),
                "arctangent_approximation": str(eps0),
                "first_index_correction": str(eps1),
                "arctangent_error": str(eps - eps0),
                "corrected_error": str(eps - eps1)}
        if m <= 3:
            j = 2 * m + 1
            independent = S_derivative_mellin(zero, j)
            root["independent_mellin_residual"] = str(independent)
            assert abs(independent) < mp.mpf(10) ** (-min(dps // 3, 12))
        records["roots"].append(root)
        print(f"root m={m}: {mp.nstr(zero, 24)}", flush=True)
    return records


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--numeric', action='store_true')
    parser.add_argument('--full', action='store_true')
    parser.add_argument('--resume', action='store_true',
                        help='Keep completed numerical records in --output; add missing roots.')
    parser.add_argument('--dps', type=int, default=45)
    parser.add_argument('--output', type=Path,
                        help='Output JSON (default: data/gaussian_order_verification.json for numerical mode, '
                             'data/gaussian_exact.json otherwise).')
    args = parser.parse_args()
    if args.output is None:
        args.output = Path(__file__).resolve().parents[1]/'data'/(
            'gaussian_order_verification.json' if args.numeric else 'gaussian_exact.json')
    result = {"exact": exact_checks()}
    print('Exact recurrence and rational-bound checks passed.', flush=True)
    if args.numeric:
        old_records = None
        if args.resume and args.output.exists():
            old_records = json.loads(args.output.read_text()).get('numeric')
        result["numeric"] = numeric_checks(args.dps, args.full, old_records)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(f'Wrote {args.output}', flush=True)


if __name__ == '__main__':
    main()
