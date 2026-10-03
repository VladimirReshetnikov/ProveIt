#!/usr/bin/env python3
"""Exact checks for the finite-model inverse correction in Section 10.

Requires SymPy only; imports no report scripts and writes no files.
The symbolic constant c represents log(C). These checks supplement the proof;
they provide neither numerical certification nor an enclosure for C.
"""
import sympy as s


def main():
    w = s.Symbol('w', positive=True)
    c = s.Symbol('c', real=True)
    h = s.Symbol('h')
    d = w / (1 + w)
    g = w**2 / 2 - s.log(1 + w) / 2
    q = g + c
    a = s.cancel(d * s.diff(g, w))
    p1 = -w**2 * (26*w**2 + 67*w + 46) / (24*(1+w)**3)
    p2 = -w**2 * (
        12*w**6 + 100*w**5 + 310*w**4 + 457*w**3
        + 310*w**2 + 36*w - 54
    ) / (48*(1+w)**6)
    B = a*q/w**2 - d*q**2/(2*w**3) - p1/w
    delta0 = -q / w

    # Solve the triangular coefficient equation independently for B.
    b = s.Symbol('b')
    equation = w*b + d*delta0**2/2 + a*delta0 + p1
    derived_B = s.solve(equation, b)[0]
    assert s.simplify(derived_B - B) == 0
    print('Triangular B identity with symbolic c=log(C): PASS')

    # h=1/v.  F(v+delta)-F(v) begins w*delta+d*h*delta^2/2;
    # q(W(v+delta)) begins q+a*h*delta; p1 correction begins h*p1.
    delta = delta0 + h*B
    log_residual = s.expand(
        w*delta + q + h*(d*delta**2/2 + a*delta + p1)
    )
    assert s.simplify(log_residual.coeff(h, 0)) == 0
    assert s.simplify(log_residual.coeff(h, 1)) == 0
    print('Reversion log residual coefficients at h^0 and h^1: PASS')

    leading = s.limit(B/w, w, s.oo)
    assert leading == s.Rational(3, 8)
    assert s.limit(delta0/w, w, s.oo) == -s.Rational(1, 2)
    print('Exact limit B(w)/w =', leading)
    print('Exact limit delta0(w)/w = -1/2')

    def scaled_derivative(f, power):
        # d/dx [x^-power f(W(x))] = x^(-power-1) D_power(f).
        return s.cancel(d*s.diff(f, w) - power*f)

    def check_growth(label, f, expected_degree):
        numerator, denominator = s.cancel(f).as_numer_denom()
        degree = s.degree(numerator, w) - s.degree(denominator, w)
        assert degree <= expected_degree
        # All poles in these rational derivative coefficients are at w=-1.
        for factor, _ in s.factor_list(denominator, w)[1]:
            assert factor == w + 1
        print('%s: rational growth degree %s <= %s; no poles for w>=1'
              % (label, degree, expected_degree))

    # Bounds used in the Taylor residual and local Newton proof.
    F2_coefficient = d                       # F'' = x^-1*d
    F3_coefficient = scaled_derivative(d, 1) # F''' = x^-2*D_1(d)
    q1_coefficient = a                       # (q o W)' = x^-1*a
    q2_coefficient = scaled_derivative(a, 1)
    p1first = scaled_derivative(p1, 1)
    p1second = scaled_derivative(p1first, 2)
    p2first = scaled_derivative(p2, 2)
    p2second = scaled_derivative(p2first, 3)
    for label, coefficient, degree in [
        ('F second derivative coefficient', F2_coefficient, 0),
        ('F third derivative coefficient', F3_coefficient, 0),
        ('q first derivative coefficient', q1_coefficient, 1),
        ('q second derivative coefficient', q2_coefficient, 1),
        ('p1/x first derivative coefficient', p1first, 1),
        ('p1/x second derivative coefficient', p1second, 1),
        ('p2 coefficient', p2, 2),
        ('p2/x^2 second derivative coefficient', p2second, 2),
    ]:
        check_growth(label, coefficient, degree)
    print('ALL EXACT INVERSE CHECKS PASS')


if __name__ == '__main__':
    main()
