#!/usr/bin/env python3
"""Exact finite-order nonautonomous Airy coefficient generator.

--order M means the epsilon recurrence residual is killed through degree M.
The output includes forward logarithmic/relative coefficients through M-3.
Polynomial inversion uses the triangular operator with diagonal 4*d+2.
No claimed analytic remainder estimate is tested by this formal calculation.
"""
if not __debug__:
    raise RuntimeError("Run with assertions enabled; do not use python -O")

import argparse
import json
from pathlib import Path

import sympy as S


def generate(order):
    if order < 4:
        raise ValueError("--order must be at least 4")
    x, a = S.symbols("x a")
    zero = (S.Integer(0), S.Integer(0))

    def add(u, v):
        return tuple(S.expand(b + c) for b, c in zip(u, v))

    def scale(u, c):
        return tuple(S.expand(b * c) for b in u)

    def diff(u):
        return (S.expand(S.diff(u[0], x) + 2 * (x + a) * u[1]),
                S.expand(u[0] + S.diff(u[1], x)))

    def conv(u, v, degree=order):
        out = [S.Integer(0)] * (degree + 1)
        for i, b in enumerate(u):
            for j, c in enumerate(v):
                if i + j <= degree and b != 0 and c != 0:
                    out[i + j] += b * c
        return [S.expand(t) for t in out]

    def power(u, k):
        out = [S.Integer(1)] + [S.Integer(0)] * order
        for _ in range(k):
            out = conv(out, u)
        return out

    def binseries(q):
        out = [S.Integer(0)] * (order + 1)
        for j in range(order // 3 + 1):
            out[3 * j] = S.rf(q, j) / S.factorial(j)
        return out

    def logseries(u, degree):
        assert u[0] == 1
        v = list(u[:degree + 1]); v[0] = S.Integer(0)
        out = [S.Integer(0)] * (degree + 1)
        term = [S.Integer(1)] + [S.Integer(0)] * degree
        for j in range(1, degree + 1):
            term = conv(term, v, degree)
            if not any(term):
                break
            out = [S.expand(b + S.Rational((-1)**(j + 1), j) * c)
                   for b, c in zip(out, term)]
        return out

    dilation = binseries(S.Rational(1, 3))
    denominator = [S.Integer(1), 0, x, -1] + [0] * (order - 3)
    inverse_denominator = [S.Integer(1)] + [S.Integer(0)] * order
    for n in range(1, order + 1):
        inverse_denominator[n] = S.expand(-sum(
            denominator[k] * inverse_denominator[n - k]
            for k in range(1, n + 1)))
    b = conv([1, 0, -x, 3] + [0] * (order - 3), inverse_denominator)
    shift_powers = {}
    for sign in (-1, 1):
        delta = [S.expand(x * c) for c in dilation]
        delta[0] -= x
        for n in range(1, order + 1):
            delta[n] += sign * dilation[n - 1]
        shift_powers[sign] = [power(delta, k) for k in range(order + 1)]

    profiles = {0: (S.Integer(1), S.Integer(0))}
    scalars = {2: a}
    shifted_cache = {}

    def shifted(k, sign):
        key = (k, sign)
        if key in shifted_cache:
            return shifted_cache[key]
        degree = order - k
        out = [zero] * (order + 1)
        derivative = profiles[k]
        for r in range(degree + 1):
            for j, c in enumerate(shift_powers[sign][r]):
                if j <= degree and c != 0:
                    out[j] = add(out[j], scale(derivative, c / S.factorial(r)))
            derivative = diff(derivative)
        dilation_factor = binseries(S.Rational(k, 3))
        result = [zero] * (order + 1)
        for i, u in enumerate(out):
            if u == zero:
                continue
            for j, c in enumerate(dilation_factor):
                if i + j + k <= order and c != 0:
                    result[i + j + k] = add(result[i + j + k], scale(u, c))
        shifted_cache[key] = result
        return result

    def residual(n):
        out = zero
        for k, profile in profiles.items():
            minus, plus = shifted(k, -1), shifted(k, 1)
            out = add(out, plus[n])
            for j in range(n + 1):
                if b[j] != 0:
                    out = add(out, scale(minus[n - j], b[j]))
            if k == n:
                out = add(out, scale(profile, -2))
            if n - k in scalars:
                out = add(out, scale(profile, -2 * scalars[n - k]))
        return out

    def invert_triangular(rhs):
        polynomial = S.Poly(S.expand(rhs), x)
        remainder = polynomial.as_expr()
        Q = S.Integer(0)
        for degree in range(max(polynomial.degree(), 0), -1, -1):
            c = S.expand(remainder).coeff(x, degree) / S.Integer(4 * degree + 2)
            term = c * x**degree
            Q += term
            image = -S.diff(term, x, 3) / 2 + 4 * (x + a) * S.diff(term, x) + 2 * term
            remainder = S.expand(remainder - image)
        assert remainder == 0
        return S.expand(Q)

    assert residual(2) == zero
    checks = []
    for m in range(3, order + 1):
        R, B = residual(m)
        Q0 = invert_triangular(-R + S.diff(B, x) / 2)
        sm = S.expand(-Q0.subs(x, 0))
        Q = S.expand(Q0 + sm)
        P = S.integrate(S.expand((-B - S.diff(Q, x, 2)) / 2), x)
        P = S.expand(P - P.subs(x, 0) - S.diff(Q, x).subs(x, 0))
        profiles[m - 2] = (P, Q)
        scalars[m] = sm
        assert residual(m) == zero, m
        assert Q.subs(x, 0) == 0
        assert S.expand(P.subs(x, 0) + S.diff(Q, x).subs(x, 0)) == 0
        assert all((da + m) % 3 == 0 for (da,), c in S.Poly(sm, a).terms() if c)
        assert all((dx + da + m - 2) % 3 == 0
                   for (dx, da), c in S.Poly(P, x, a).terms() if c)
        assert all((dx + da + m - 3) % 3 == 0
                   for (dx, da), c in S.Poly(Q, x, a).terms() if c)
        checks.append(f"epsilon^{m}: recurrence, boundary, derivative, grading exact")
        print(f"order {m}: s_{m} = {S.factor(sm)}", flush=True)

    # Adding later profiles must not alter already-cancelled lower orders.
    assert all(residual(m) == zero for m in range(order + 1))
    correction_order = order - 3
    ratio = [S.Integer(1)] + [scalars.get(m, S.Integer(0)) for m in range(1, order + 1)]
    logratio = logseries(ratio, order)
    base = [S.Integer(0)] * (order + 1)
    for j in range(1, (order + 1) // 3 + 1):
        if 3 * j - 1 <= order:
            base[3 * j - 1] = 3 * a * (-1)**(j + 1) * S.binomial(S.Rational(1, 3), j)
        if 3 * j <= order:
            base[3 * j] = S.Rational(4, 3 * j)
    amplitude_log = {}
    for k in range(1, correction_order + 1):
        m = k + 3
        coefficient = base[m] - logratio[m]
        for j, hj in amplitude_log.items():
            if (m - j) % 3 == 0:
                r = (m - j) // 3
                coefficient -= hj * S.rf(S.Rational(j, 3), r) / S.factorial(r)
        amplitude_log[k] = S.expand(3 * coefficient / k)
    for m in range(2, order + 1):
        coefficient = base[m] - logratio[m]
        for k, hk in amplitude_log.items():
            if m > k and (m - k) % 3 == 0:
                r = (m - k) // 3
                coefficient -= hk * S.rf(S.Rational(k, 3), r) / S.factorial(r)
        assert S.expand(coefficient) == 0, (m, coefficient)

    # F(0)=0, F'(0)=1, F''=2(x+a)F, evaluated at x=epsilon.
    epsilon = S.symbols("epsilon")
    F = [S.Integer(0), S.Integer(1)]
    for n in range(correction_order):
        F.append(S.expand((2 * a * F[n] + (2 * F[n - 1] if n else 0))
                          / ((n + 2) * (n + 1))))
    Fe = sum(c * epsilon**j for j, c in enumerate(F))
    Fpe = S.diff(Fe, epsilon)
    endpoint_expr = S.expand(sum(
        epsilon**k * (P.subs(x, epsilon) * Fe + Q.subs(x, epsilon) * Fpe)
        for k, (P, Q) in profiles.items()) / epsilon)
    endpoint = [S.expand(endpoint_expr).coeff(epsilon, k)
                for k in range(correction_order + 1)]
    endpoint_log = logseries(endpoint, correction_order)
    combined = {k: S.expand(amplitude_log[k] + endpoint_log[k])
                for k in range(1, correction_order + 1)}
    z = S.symbols("z")
    log_n = {}
    for k, expression in combined.items():
        expression_n = S.Integer(0)
        for (degree,), coefficient in S.Poly(expression, a).terms():
            if coefficient:
                assert (degree + k) % 3 == 0
                expression_n += coefficient * S.Rational(2)**(-(degree + k) // 3) * z**degree
        log_n[k] = S.expand(expression_n)
    relative = {0: S.Integer(1)}
    for k in range(1, correction_order + 1):
        relative[k] = S.expand(sum(j * log_n[j] * relative[k - j]
                                  for j in range(1, k + 1)) / k)

    expected_s = {2: a, 3: S.Rational(4, 3), 4: 29 * a*a / 270,
                  5: -23 * a / 81, 6: (74385 - 8783 * a**3) / 85050}
    expected_log = {1: 53 * z*z / 90, 2: 44 * z / 27,
                    3: S.Rational(141, 140) - 1304 * z**3 / 42525}
    for k, expected in expected_s.items():
        if k in scalars:
            assert S.expand(scalars[k] - expected) == 0
    for k, expected in expected_log.items():
        if k in log_n:
            assert S.expand(log_n[k] - expected) == 0
    encode = lambda d: {str(k): str(S.factor(v)) for k, v in d.items()}
    return {"passed": True, "epsilon_residual_order": order,
            "forward_correction_order": correction_order,
            "normalization": "G0=F; Gk(0)=Gk'(0)=0; H_N/H_(N-1)=2(1+sum s_m epsilon^m)",
            "s": encode(scalars),
            "profiles": {str(k): {"P": str(S.factor(P)), "Q": str(S.factor(Q))}
                         for k, (P, Q) in profiles.items()},
            "amplitude_log_N": encode(amplitude_log),
            "endpoint_log_N": encode({k: endpoint_log[k] for k in combined}),
            "forward_log_N": encode(combined), "forward_log_n": encode(log_n),
            "forward_relative_n": encode({k: relative[k] for k in log_n}),
            "checks": checks,
            "limitation": "Exact formal algebra only; no analytic asymptotic remainder or gamma certification"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--order", type=int, default=8)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parent / "output" / "coefficients.json")
    args = parser.parse_args()
    result = generate(args.order)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(f"All exact formal checks passed; output: {args.output}")


if __name__ == "__main__":
    main()
