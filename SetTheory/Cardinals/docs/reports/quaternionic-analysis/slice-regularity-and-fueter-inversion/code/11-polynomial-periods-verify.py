#!/usr/bin/env python3
"""Finite symbolic and numerical checks for Polynomial Periods.

These tests are independent diagnostics, not substitutes for the all-order
proofs in article.tex. Numerical integration is not a certified zero test.
Requires Python 3.10+, SymPy, mpmath. Run from any working directory.
"""
from __future__ import annotations
import argparse
import json
import math
import time
from pathlib import Path
import sympy as sp
import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
x, y, t = sp.symbols('x y t', real=True)
z = x + sp.I*y
zb = x - sp.I*y


def kappa(h: int) -> sp.Rational:
    return sp.Rational((-1)**(h+1), 2**(2*h-1)*math.factorial(h)*math.factorial(h-1))


def c_h(h: int) -> int:
    return 2**h*math.factorial(h)


def radial_pair(h: int, f: sp.Expr) -> tuple[sp.Expr, sp.Expr]:
    f = sp.expand_complex(f).expand()
    a, b = sp.re(f).expand(), sp.im(f).expand()
    for _ in range(h):
        a = sp.diff(a, y)/y
        b = sp.diff(b/y, y)
        a, b = sp.cancel(a), sp.cancel(b)
    return sp.expand(c_h(h)*a), sp.expand(c_h(h)*b)


def current(h: int, p: sp.Expr, q: sp.Expr) -> tuple[sp.Expr, sp.Expr]:
    factor = kappa(h)*((t-x)**2+y*y)**(h-1)
    return (sp.expand(factor*((x-t)*p+y*q)),
            sp.expand(factor*(y*p-(x-t)*q)))


def assert_zero(expr: sp.Expr, label: str) -> None:
    if sp.cancel(sp.expand(expr)) != 0:
        raise AssertionError(label + ': ' + str(sp.factor(expr)))


def symbolic_checks(full: bool) -> dict:
    result = {}
    P, Q, Px, Py, Qx, Qy = sp.symbols('P Q Px Py Qx Qy')
    for h in range(1, 9):
        a, b = current(h, P, Q)
        bx = sp.diff(b, x)+sp.diff(b, P)*Px+sp.diff(b, Q)*Qx
        ay = sp.diff(a, y)+sp.diff(a, P)*Py+sp.diff(a, Q)*Qy
        assert_zero((bx-ay).subs({Px: Qy+2*h*Q/y, Py: -Qx}), f'closedness h={h}')
    result['closedness_h'] = [1, 8]
    count = 0
    max_h = 5 if full else 3
    for h in range(1, max_h+1):
        modulus = sp.Poly(((t-x)**2+y*y)**h, t)
        for degree in range(2*h+6):
            H = sp.rem(sp.Poly(t**degree, t), modulus).as_expr()
            P, Q = radial_pair(h, z**degree)
            a, b = current(h, P, Q)
            assert_zero(sp.diff(H, x)-a, f'H_x h={h} k={degree}')
            assert_zero(sp.diff(H, y)-b, f'H_y h={h} k={degree}')
            count += 1
    result['real_monomial_Hermite_cases'] = count
    result['real_monomial_range'] = f'1 <= h <= {max_h}; 0 <= k <= 2h+5'
    # Imaginary constants and monomials cannot be tested by polynomial division
    # over the reals; construct the two-node Hermite interpolant explicitly.
    w = sp.symbols('w')
    imaginary_cases = []
    for h in range(1, 4):
        degrees = list(range(2*h+2)) if h <= 2 else [0, 1, 3]
        for degree in degrees:
            f = sp.I*w**degree
            H = 0
            for j in range(h):
                left = sp.diff(f/(w-zb)**h, w, j).subs(w, z)/math.factorial(j)
                right = sp.diff(-f/(w-z)**h, w, j).subs(w, zb)/math.factorial(j)
                H += (t-zb)**h*left*(t-z)**j+(t-z)**h*right*(t-zb)**j
            H = sp.cancel(sp.expand(H))
            P, Q = radial_pair(h, sp.I*z**degree)
            a, b = current(h, P, Q)
            assert_zero(sp.diff(H, x)-a, f'imag H_x h={h} k={degree}')
            assert_zero(sp.diff(H, y)-b, f'imag H_y h={h} k={degree}')
            imaginary_cases.append([h, degree])
    result['imaginary_monomial_cases'] = imaginary_cases
    for h in range(1, 9):
        assert_zero(kappa(h)*(-1)**h*c_h(h)**2+2*h, 'calibration')
        for r in range(h):
            s = h-r
            gamma = (-kappa(h)/2*sp.Rational(math.factorial(h-1), math.factorial(s-1))
                     *(-1)**(s-1)*(2*sp.I)**h*sp.I)
            leading = c_h(h)*sp.I**(h-1)*(-1)**(s-1)*math.factorial(s-1)/(2*sp.pi)
            assert_zero(2*sp.pi*gamma*leading-1, 'residue asymptotic phase')
    result['normalization_h'] = [1, 8]
    return result


def derivative_value(coefficients: list[mp.mpf], argument: mp.mpc, order: int) -> mp.mpc:
    # Horner evaluation of the differentiated polynomial.
    value = mp.mpc(0)
    for k in range(len(coefficients)-1, order-1, -1):
        value = value*argument+coefficients[k]*math.factorial(k)/math.factorial(k-order)
    return value


def log_target(h: int, coeffs: list[mp.mpf], center: mp.mpc,
               rho: mp.mpf, theta: mp.mpf) -> tuple[mp.mpf, mp.mpf]:
    point = center+rho*mp.exp(mp.j*theta)
    Y = point.imag
    log_jet = [mp.log(rho)+mp.j*theta]
    for j in range(1, h+1):
        log_jet.append((-1)**(j-1)*math.factorial(j-1)/(point-center)**j)
    fj = []
    for j in range(h+1):
        fj.append(sum(math.comb(j,l)*derivative_value(coeffs, point, j-l)*log_jet[l]
                      for l in range(j+1))/(2*mp.pi*mp.j))
    p = mp.mpf(0)
    q = mp.mpf(0)
    for j in range(h+1):
        e = mp.mpf((-1)**(h+j)*math.factorial(2*h-j))/(2**(h-j)*math.factorial(h-j)*math.factorial(j))
        q += e*Y**(j-2*h)*(mp.j**j*fj[j]).imag
        if j:
            d = mp.mpf((-1)**(h+j)*math.factorial(2*h-j-1))/(2**(h-j)*math.factorial(h-j)*math.factorial(j-1))
            p += d*Y**(j-2*h)*(mp.j**j*fj[j]).real
    return c_h(h)*p, c_h(h)*q


def r_coefficients(h: int, X: mp.mpf, Y: mp.mpf) -> list[mp.mpf]:
    coeffs = [mp.mpf(1)]
    for _ in range(h-1):
        new = [mp.mpf(0)]*(len(coeffs)+2)
        for j, val in enumerate(coeffs):
            new[j] += val*(X*X+Y*Y)
            new[j+1] -= 2*X*val
            new[j+2] += val
        coeffs = new
    return coeffs


def numerical_checks() -> dict:
    mp.mp.dps = 50
    periods = []
    n = 384
    p0 = mp.mpc(mp.mpf(1)/3, mp.mpf(5)/4)
    radius = mp.mpf(1)/5
    for h in range(1, 5):
        coeffs = [mp.mpf((-1)**j*(j+1)) for j in range(2*h)]
        sums = [mp.mpf(0)]*(2*h)
        kap = mp.mpf((-1)**(h+1))/(2**(2*h-1)*math.factorial(h)*math.factorial(h-1))
        for k in range(n):
            theta = 2*mp.pi*(mp.mpf(k)+mp.mpf('0.5'))/n
            point = p0+radius*mp.exp(mp.j*theta)
            X, Y = point.real, point.imag
            P, Q = log_target(h, coeffs, p0, radius, theta)
            dx, dy = -radius*mp.sin(theta), radius*mp.cos(theta)
            C = r_coefficients(h, X, Y)
            for j in range(2*h):
                cj = C[j] if j < len(C) else 0
                prev = C[j-1] if 0 <= j-1 < len(C) else 0
                sums[j] += kap*(((X*cj-prev)*P+Y*cj*Q)*dx
                                +(Y*cj*P+(prev-X*cj)*Q)*dy)*2*mp.pi/n
        error = max(abs(a-b) for a,b in zip(sums, coeffs))
        assert error < mp.mpf('1e-35'), (h, error)
        periods.append({'h': h, 'coefficients': [int(v) for v in coeffs],
                        'max_absolute_error': mp.nstr(error, 12)})
    asymptotics = []
    for h in range(1,5):
        for s in range(1,h+1):
            r = h-s
            coeffs = [mp.mpf(0)]*(2*r+1)
            for j in range(r+1):
                coeffs[2*j] = mp.mpf(math.comb(r,j))
            jet = abs(derivative_value(coeffs, mp.j, r))
            A = c_h(h)*math.factorial(s-1)*jet/(2*mp.pi)
            ratios = []
            for power in [2,3,4,5]:
                rho = mp.mpf(10)**(-power)
                magnitudes = []
                for k in range(96):
                    theta = 2*mp.pi*k/96
                    P,Q = log_target(h, coeffs, mp.j, rho, theta)
                    magnitudes.append(mp.sqrt(P*P+Q*Q))
                ratios.append({'radius': str(rho), 'sampled_sup_ratio': mp.nstr(rho**s*max(magnitudes)/A, 15),
                               'sampled_mean_square_ratio': mp.nstr(rho**(2*s)*sum(v*v for v in magnitudes)/(96*A*A),15)})
            assert abs(mp.mpf(ratios[-1]['sampled_sup_ratio'])-1) < mp.mpf('0.002')
            asymptotics.append({'h': h, 's': s, 'residue': f'(t^2+1)^{r}', 'A': mp.nstr(A,15), 'ratios': ratios})
    return {'precision_decimal_digits': 50, 'quadrature_nodes': n,
            'period_checks': periods, 'asymptotic_checks': asymptotics,
            'warning': 'Floating-point quadrature and sampled extrema are diagnostics, not rigorous certificates.'}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick', action='store_true', help='use fewer real-monomial symbolic tests')
    args = parser.parse_args()
    start = time.monotonic()
    print('Checking exact symbolic identities...', flush=True)
    symbolic = symbolic_checks(not args.quick)
    print('Checking periods and sharp asymptotics numerically...', flush=True)
    numerical = numerical_checks()
    result = {'status':'PASS', 'sympy':sp.__version__, 'mpmath':mp.__version__,
              'symbolic':symbolic, 'numerical':numerical,
              'elapsed_seconds':round(time.monotonic()-start,3),
              'scope':'Finite tests only; the general proofs are in article.tex.'}
    output = ROOT/'data'/'verification.json'
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps(result,indent=2)+'\n', encoding='utf-8')
    print(json.dumps({'status':result['status'], 'symbolic':symbolic,
                      'period_errors':[v['max_absolute_error'] for v in numerical['period_checks']],
                      'elapsed_seconds':result['elapsed_seconds']},indent=2))
    print('Saved', output)

if __name__ == '__main__':
    main()
