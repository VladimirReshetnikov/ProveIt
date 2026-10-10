#!/usr/bin/env python3
"""Independent diagnostics for the six-cone theorem and triple finite part.

These are numerical diagnostics, not interval certificates or proofs.
The default run compares a local digamma subtraction with an independent
Mellin/polylog-order formula, and tests the pre-pole spectral identity
against exact piecewise Bernoulli-polynomial integration.
"""
import argparse
import json
from pathlib import Path
import mpmath as mp
import sympy as sp


class OrderZeroPolylog:
    """Li'_0(exp(-t+i theta)) using two convergent series.

    Near the unit circle, differentiate Jonquiere's expansion (|log z|<2pi).
    For t>2 use the absolutely convergent defining power series.  The
    truncations are deliberately generous, but are not interval bounds.
    """
    def __init__(self, digits):
        self.count = 6 * digits + 30
        self.coeff = [-mp.log(2 * mp.pi) / 2]
        for k in range(1, self.count):
            if k % 2 == 0:
                value = (-1) ** (k // 2) * mp.zeta(k + 1)
                value /= 2 * (2 * mp.pi) ** k
            else:
                base = -2 * (-1) ** ((k - 1) // 2)
                base *= mp.zeta(k + 1) / (2 * mp.pi) ** (k + 1)
                value = base * (mp.log(2 * mp.pi) - mp.digamma(k + 1)
                                - mp.zeta(k + 1, derivative=1) / mp.zeta(k + 1))
            self.coeff.append(value)
        self.logs = [mp.mpf(0)] + [mp.log(n) for n in range(1, self.count + 1)]

    def evaluate(self, t, theta, derivative=False):
        z = mp.exp(-t + 1j * theta)
        if t <= 2:
            mu = -t + 1j * theta
            w = -mu
            value = (mp.euler + mp.log(w)) / w
            value += mp.polyval(list(reversed(self.coeff)), mu)
            if derivative:
                deriv = (1 - mp.euler - mp.log(w)) / w**2
                coeff_d = [k * self.coeff[k] for k in range(1, len(self.coeff))]
                deriv -= mp.polyval(list(reversed(coeff_d)), mu)
                return value, deriv
            return value
        total = mp.mpc(0)
        zpower = z
        for n in range(1, self.count):
            term = -self.logs[n] * zpower
            total += term
            if n > 3 and abs(term) < mp.eps * mp.mpf('0.001'):
                break
            zpower *= z
        return total


def mellin_cone_zero(theta, phi, engine):
    L = mp.euler + mp.log(2 * mp.pi)
    A = L + 1j * mp.pi / 2

    def F(t, angle):
        if t > (mp.mp.dps + 20) * mp.log(10):
            return mp.mpc(0)
        z = mp.exp(-t + 1j * angle)
        return engine.evaluate(t, angle) - A * z / (1 - z)

    fx, fy = F(0, theta), F(0, phi)
    zx, zy = mp.exp(1j * theta), mp.exp(1j * phi)
    dx = engine.evaluate(0, theta, True)[1] + A * zx / (1 - zx)**2
    dy = engine.evaluate(0, phi, True)[1] + A * zy / (1 - zy)**2
    h0, dh0 = fx * fy, dx * fy + fx * dy
    tiny = mp.power(10, -(mp.mp.dps // 2))

    def first(t):
        if abs(t) < tiny:
            return dh0
        return (F(t, theta) * F(t, phi) - h0) / t

    def tail(t):
        return F(t, theta) * F(t, phi) / t

    integral = mp.quad(first, [0, mp.mpf('0.25'), 1])
    integral += mp.quad(tail, [1, 2, 4, 8, mp.inf])
    return integral + (-mp.log(2 * mp.pi) + 1j * mp.pi / 2) * h0


def triple_gamma0_mellin(shifts, engine):
    result = mp.mpc(0)
    for k in range(3):
        i, j = [r for r in range(3) if r != k]
        theta = mp.arg(mp.exp(2j * mp.pi * (shifts[i] - shifts[k])))
        phi = mp.arg(mp.exp(2j * mp.pi * (shifts[j] - shifts[k])))
        result += mellin_cone_zero(theta, phi, engine)
    return 2 * mp.re(result)


def triple_gamma0_local(shifts):
    points = sorted((mp.frac(-a), k) for k, a in enumerate(shifts))
    result = mp.mpf(0)
    tiny = mp.power(10, -(mp.mp.dps // 2))
    for r, (x, k) in enumerate(points):
        right = points[r + 1][0] if r + 1 < len(points) else points[0][0] + 1
        width = right - x
        args = [mp.frac(a - shifts[k]) for j, a in enumerate(shifts) if j != k]

        def P(t):
            return mp.fprod(-mp.digamma(a + t) for a in args)

        p0 = P(0)
        p1 = sum(-mp.polygamma(1, args[j]) * (-mp.digamma(args[1 - j]))
                 for j in range(2))

        def regular(t):
            if abs(t) < tiny:
                return p1 + mp.euler * p0
            pt = P(t)
            return (pt - p0) / t - mp.digamma(1 + t) * pt

        result += mp.quad(regular, [0, width / 2, width]) + p0 * mp.log(width)
    return result


def bernoulli_integral(lambdas, shifts):
    x = sp.Symbol('x')
    cuts = sorted({sp.Rational(0), sp.Rational(1)} |
                  {sp.frac(-a) for a in shifts})
    total = sp.Rational(0)
    for left, right in zip(cuts, cuts[1:]):
        mid = (left + right) / 2
        factors = [-sp.bernoulli(lam, x + a - sp.floor(mid + a)) / lam
                   for lam, a in zip(lambdas, shifts)]
        total += sp.integrate(sp.prod(factors), (x, left, right))
    return sp.simplify(total)


def spectral_mellin(lambdas, shifts):
    result = mp.mpc(0)
    for k in range(3):
        i, j = [r for r in range(3) if r != k]
        X = mp.exp(2j * mp.pi * (shifts[i] - shifts[k]))
        Y = mp.exp(2j * mp.pi * (shifts[j] - shifts[k]))
        A, B, C = lambdas[i], lambdas[j], lambdas[k]
        def integrand(t):
            if t > (mp.mp.dps + 20) * mp.log(10):
                return mp.mpc(0)
            return t**(C - 1) * mp.polylog(A, X * mp.exp(-t)) * mp.polylog(B, Y * mp.exp(-t))
        value = mp.quad(integrand, [0, 1, 3, 8, mp.inf]) / mp.gamma(C)
        result += 2 * mp.re(mp.exp(-1j * mp.pi * (A + B - C) / 2) * value)
    return result * mp.fprod(mp.gamma(lam) for lam in lambdas) / (2 * mp.pi)**sum(lambdas)


def run(digits):
    mp.mp.dps = digits + 10
    engine = OrderZeroPolylog(digits + 10)
    checks = []
    for t, theta in [(mp.mpf('0.2'), mp.mpf('1.1')),
                     (mp.mpf('1.7'), mp.mpf('-2.8')),
                     (mp.mpf('2.3'), mp.mpf('2.0'))]:
        z = mp.exp(-t + 1j * theta)
        observed = engine.evaluate(t, theta)
        reference = mp.diff(lambda s: mp.polylog(s, z), 0)
        error = abs(observed - reference)
        assert error < mp.power(10, -digits), error
        checks.append({'check': 'order_zero_polylog', 't': str(t),
                       'error': mp.nstr(error, 8)})
    # The first case has a nonzero exact rational integral, detecting phase errors.
    rational_shifts = [sp.Rational(0), sp.Rational(1, 5), sp.Rational(7, 10)]
    shifts = [mp.mpf(str(a.p)) / int(a.q) for a in rational_shifts]
    for lambdas in [(1, 1, 1), (2, 1, 3)]:
        exact = bernoulli_integral(lambdas, rational_shifts)
        observed = spectral_mellin(lambdas, shifts)
        reference = mp.mpf(str(exact.p)) / int(exact.q)
        error = abs(observed - reference)
        assert error < mp.power(10, -digits), error
        checks.append({'check': 'six_cone_bernoulli', 'lambda': lambdas,
                       'exact': str(exact), 'error': mp.nstr(error, 8)})
    # A full comparison at the triple Stieltjes pole, using independent integrands.
    shifts = [mp.mpf(0), mp.mpf(1) / 3, mp.mpf(2) / 3]
    local = triple_gamma0_local(shifts)
    mellin = triple_gamma0_mellin(shifts, engine)
    error = abs(local - mellin)
    assert error < mp.power(10, -digits + 3), error
    checks.append({'check': 'triple_gamma0_finite_part',
                   'shifts': ['0', '1/3', '2/3'],
                   'local': mp.nstr(local, digits), 'mellin': mp.nstr(mellin, digits),
                   'digamma_product': mp.nstr(-local, digits),
                   'error': mp.nstr(error, 8)})
    return {'precision_digits': mp.mp.dps, 'requested_agreement_digits': digits,
            'interpretation': 'Independent floating-point diagnostics; not rigorous enclosures.',
            'checks': checks, 'passed': True}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--digits', type=int, default=32)
    parser.add_argument('--output', default='../data/trilinear_checks.json')
    args = parser.parse_args()
    result = run(args.digits)
    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
