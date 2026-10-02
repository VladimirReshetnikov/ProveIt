#!/usr/bin/env python3
"""Exact symbolic replay of the first A215570 correction and kernel sextic.

This checks finite algebraic manipulations in the manuscript. It does not
replace the analytic remainder proof or certify the conjectured recurrence.
"""
from pathlib import Path
import sympy as S


def main() -> None:
    r = 5
    p = [S.Rational(1, r)] * r
    steps = list(range(-2, 3))
    d = r - 2
    variance = sum(p[i] * steps[i]**2 for i in range(r))
    # Residual composition markers, with their projections on 1 and s removed.
    residual = S.Matrix([
        [int(i == a) - p[a] - p[a]*steps[a]*steps[i]/variance
         for i in range(r)] for a in range(d)
    ])
    hessian = S.Matrix(d, d, lambda a, b:
        sum(p[i]*residual[a, i]*residual[b, i] for i in range(r)))
    covariance = hessian.inv()
    cubic = [[[sum(p[i]*residual[a,i]*residual[b,i]*residual[c,i]
                    for i in range(r)) for c in range(d)]
              for b in range(d)] for a in range(d)]
    v_second = S.Matrix(d, d, lambda a, b:
        -sum(p[i]*steps[i]*residual[a,i]*residual[b,i]
             for i in range(r))/variance)
    q_first = S.Matrix(r, d, lambda i, a: p[i]*residual[a,i])
    q_second = [S.Matrix(d, d, lambda a, b:
        p[i]*(residual[a,i]*residual[b,i] + steps[i]*v_second[a,b]
              - hessian[a,b])) for i in range(r)]

    q = S.symbols('q:5', positive=True)
    a, e, bcrit = q[0], q[4], q[3] + 2*q[4]
    kappa = 2/(bcrit + S.sqrt(bcrit*bcrit - 4*a*e))
    log_kappa = S.log(kappa)
    base = dict(zip(q, p))
    grad = S.Matrix([S.diff(log_kappa, qi).subs(base).simplify() for qi in q])
    second = S.Matrix(r, r, lambda i,j:
        S.diff(log_kappa, q[i], q[j]).subs(base).simplify())
    ell_first = (q_first.T*grad).applyfunc(S.simplify)
    ell_second = (q_first.T*second*q_first +
        sum((grad[i]*q_second[i] for i in range(r)), S.zeros(d,d))
        ).applyfunc(S.simplify)
    hc_first = [-sum(p[i]*steps[i]**2*residual[a,i] for i in range(r)) /
                (2*variance) for a in range(d)]

    u = S.symbols('u')
    step_poly = sum(p[i]*u**steps[i] for i in range(r))
    inner_root = (-3 + S.sqrt(5))/2
    l2 = S.simplify(1 + 1/(inner_root*S.diff(step_poly,u).subs(u,inner_root)))
    length_correction = S.simplify(-S.Rational(3,2)*l2 - 1/(2*variance))
    saddle_correction = (
        -sum(covariance[a,b]*(ell_second[a,b]+ell_first[a]*ell_first[b])/2
             for a in range(d) for b in range(d))
        -sum(covariance[a,b]*ell_first[a]*hc_first[b]
             for a in range(d) for b in range(d))
        +sum(ell_first[a]*cubic[b][c][e]*covariance[a,b]*covariance[c,e]/2
             for a in range(d) for b in range(d) for c in range(d) for e in range(d)))
    saddle_correction = S.simplify(saddle_correction)
    delta = S.simplify(length_correction + saddle_correction)
    alpha = S.simplify((S.Rational(1,r)-r)/12 + delta/r)
    assert variance == 2
    assert hessian.det() == S.Rational(1,6250)
    assert S.simplify(saddle_correction + S.Rational(11,4) - S.sqrt(5)) == 0
    assert S.simplify(delta + S.Rational(9,2) - 13*S.sqrt(5)/10) == 0
    assert S.simplify(alpha - 13*(S.sqrt(5)-5)/50) == 0

    # Exact elimination of the two quadratic kernel factors.
    aa, bb, cc, dd, ee, x = S.symbols('a b c d e X')
    small_product, large_product = -aa*x, -1/(ee*x)
    v = (dd*small_product-bb)/(ee*(large_product-small_product))
    w = -dd/ee-v
    equation = S.factor(small_product+large_product+v*w-(cc-1)/ee)
    numerator, _ = S.fraction(equation)
    sextic = (aa**3*ee**3*x**6 + aa**2*ee**2*(cc-1)*x**5 +
              (aa*bb*dd*ee-aa**2*ee**2)*x**4 +
              (aa*dd**2+bb**2*ee+2*aa*ee*(1-cc))*x**3 +
              (bb*dd-aa*ee)*x**2 + (cc-1)*x + 1)
    assert S.expand(numerator + sextic) == 0

    lines = [
        'EXACT SYMBOLIC CHECKS',
        f'Variance = {variance}', f'Hessian = {hessian}',
        f'Inverse Hessian = {covariance}',
        f'Gradient log kappa = {ell_first}',
        f'Hessian log kappa = {ell_second}',
        f'Gradient log c = {hc_first}', f'L2 = {l2}',
        f'Length correction = {length_correction}',
        f'Saddle correction = {saddle_correction}',
        f'Delta (length N normalization) = {delta}',
        f'alpha_5_1 = {alpha}',
        'PASS alpha_5_1 = 13*(sqrt(5)-5)/50',
        'PASS exact symbolic derivation of the multivariate sextic',
        f'Sextic = {S.Poly(sextic,x)}',
        'No conjectured recurrence was used.',
    ]
    out = Path(__file__).resolve().parents[1]/'data'
    out.mkdir(exist_ok=True)
    (out/'symbolic_verification.txt').write_text('\n'.join(lines)+'\n')
    print('\n'.join(lines))

if __name__ == '__main__':
    main()
