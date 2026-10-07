#!/usr/bin/env python3
"""Reproduce exact algebra and finite numerical checks for the Fourier frontiers.

Requirements: Python 3.10+, numpy, scipy, sympy.
Run from any directory, for example:
  python verify_frontiers.py --output frontiers_checks.json

The symbolic checks certify the listed polynomial/rational identities. The
finite measure and LP checks are independent diagnostics, not substitutes
for the continuum positivity, existence, or uniqueness proofs in the paper.
The LP discretizes the cosine interval and thus supplies an upper bound for
the continuum minimum, up to the solver's numerical tolerance.
"""
from __future__ import annotations

import argparse
import json
from math import acos, cos, pi, sqrt, tan
from pathlib import Path

import numpy as np
import sympy as sp
from numpy.polynomial.chebyshev import chebvander
from scipy.optimize import brentq, linprog


C_MINUS = (1 - sqrt(5)) / 4
C_PLUS = (sqrt(5) - 1) / 4


def transition_polynomial(c: float) -> float:
    return -1 + 5*c + 11*c*c - 6*c**3 - 12*c**4


C_STAR = brentq(transition_polynomial, 0, 1/6, xtol=1e-15)
A_STAR = acos(C_STAR)


def cubic(c: float, v: float) -> float:
    return (4*(1-c)*(1+2*c)*v**3 + 4*c*(1-c)*(1+2*c)*v**2
            + (1+c)*(4*c*c-3)*v + c*(4*c*c-3))


def branch_root(c: float) -> float:
    lo, hi = -1.0, -sqrt(3)/2
    if abs(cubic(c, lo)) < 2e-13:
        return lo
    if abs(cubic(c, hi)) < 2e-13:
        return hi
    return brentq(lambda v: cubic(c, v), lo, hi, xtol=1e-14)


def frontier(a: float) -> float:
    c = cos(a)
    if a <= pi/5:
        return 0.0
    if a <= 2*pi/5:
        return (1+2*c-4*c*c)/(3+10*c-12*c*c)
    if a <= A_STAR:
        return (1-2*c*c)/(3+2*c-4*c*c)
    if a <= 3*pi/5:
        v = branch_root(c)
        return (1+2*c*v)/(1-2*c-2*v)
    if a <= 5*pi/7:
        return 2*c*(c-1)/(2*c*c-2*c+1)
    if a <= 4*pi/5:
        z, w = -c, cos(4*(pi-a))
        return (z-w)/(2-z-w)
    return -c


def extremizer(a: float) -> tuple[np.ndarray, np.ndarray]:
    """Return cosine nodes and total masses of the asserted even measure."""
    c, rho = cos(a), frontier(a)
    if a <= pi/5:
        return np.array([cos(pi/5), cos(3*pi/5), -1.]), np.array([.4, .4, .2])
    if a <= 2*pi/5:
        v = -1/(4*c)
        s, d = c+v, 5-6*(c+v)
        pc = 4*v*(v-1)/(d*(c-v)*(c+1))
        pv = 4*c*(c-1)/(d*(v-c)*(v+1))
        pm = (3-4*s)*(1+2*s)/(4*d*(c+1)*(v+1))
        return np.array([c, v, -1.]), np.array([pc, pv, pm])
    if a <= A_STAR:
        v = -(c+1)/(2*c+1)
        p = (-rho-v)/(c-v)
        return np.array([c, v]), np.array([p, 1-p])
    if a <= 3*pi/5:
        v = branch_root(c)
        p = (-rho-v)/(c-v)
        return np.array([c, v]), np.array([p, 1-p])
    if a <= 5*pi/7:
        p = 1/((c+1)*(2*c*c-2*c+1))
        return np.array([c, -1.]), np.array([p, 1-p])
    if a <= 4*pi/5:
        p = 2/(2+c-cos(4*(pi-a)))
        return np.array([c, -1.]), np.array([p, 1-p])
    return np.array([c]), np.array([1.])


def exact_checks() -> list[str]:
    c, v, x, s, t, R, X = sp.symbols('c v x s t R X')
    checks: list[str] = []

    def check(name: str, expression: sp.Expr) -> None:
        result = sp.cancel(expression)
        if result != 0:
            raise AssertionError((name, result))
        checks.append(name)

    F = (4*(1-c)*(1+2*c)*v**3 + 4*c*(1-c)*(1+2*c)*v**2
         + (1+c)*(4*c*c-3)*v + c*(4*c*c-3))
    D = 1-2*c-2*v
    rho = (1+2*c*v)/D
    p = (-rho-v)/(c-v)
    raw = lambda j: p*c**j + (1-p)*v**j
    T = lambda j: sp.chebyshevt(j, x)
    moment = lambda j: p*sp.chebyshevt(j, c)+(1-p)*sp.chebyshevt(j, v)
    q1 = 2*v*(c+v)**2
    q2 = (1-c*c-2*c*v-3*v*v)/2
    q4 = sp.Rational(1, 8)
    q0 = sp.Rational(3, 8)-(c*c+2*c*v+3*v*v)/2-c*(c+2*v)*v*v
    K = -q1-q2+q4
    Q = (c-x)*(-c-2*v-x)*(x-v)**2
    P = -1+5*c+11*c*c-6*c**3-12*c**4
    H = (1+2*c*v)**2-2*(c+v)**2-2*(c+v)*c*v
    check('quartic Chebyshev expansion', Q-q0-q1*T(1)-q2*T(2)-q4*T(4))
    check('quartic calibration identity', 4*D*(rho*K+q0)-F)
    check('branch first moment', moment(1)+rho)
    check('branch second moment', moment(2)+rho)
    check('branch fourth moment equation', moment(4)-rho+2*F/D)
    check('third lower slack factorization',
          moment(3)+rho-4*(1-c)*(1-v)*((1+2*c)*v+c+1)/D)
    check('third upper slack factorization', moment(3)-rho-2*H/D)
    check('left root endpoint', F.subs(v, -1)-(1-2*c)*(4*c*c-2*c-1))
    radical = sp.sqrt(3)/2
    check('right root endpoint',
          F.subs(v, -radical)-c*c*(3+2*radical-2*c*(1+2*radical)))
    v0 = -(c+1)/(1+2*c)
    check('first continuation transition polynomial', F.subs(v, v0)-P/(1+2*c)**2)
    Fst = (s+t)*(4*s*s-4*t-3)-4*s*t*(1+2*t)
    B = (1+2*t)**2-2*s*s-2*s*t
    check('symmetric cubic expression', Fst.subs({s: c+v, t: c*v})-F)
    check('upper slack elimination', Fst+2*s*B+s+4*t*t+3*t)
    check('upper slack eliminated factors',
          B.subs(s, -t*(4*t+3))+(1+2*t)*(4*t+1)*(4*t*t+2*t-1))
    resultant = sp.resultant(F, H, v)
    check('independent upper slack resultant',
          resultant-4*(c-1)**2*(c+1)**2*(2*c+1)**2*(4*c*c-2*c-1)**2)

    vf = -1/(4*c)
    sf, df = c+vf, 5-6*(c+vf)
    rf = (1-2*sf)/df
    pc = 4*vf*(vf-1)/(df*(c-vf)*(c+1))
    pv = 4*c*(c-1)/(df*(vf-c)*(vf+1))
    pm = (3-4*sf)*(1+2*sf)/(4*df*(c+1)*(vf+1))
    check('first-window mass normalization', pc+pv+pm-1)
    for j in range(1, 5):
        check(f'first-window Fourier moment {j}',
              pc*sp.chebyshevt(j, c)+pv*sp.chebyshevt(j, vf)+pm*(-1)**j+rf)
    check('first-window rational value',
          rf-(1+2*c-4*c*c)/(3+10*c-12*c*c))
    Qf = (c-x)*(x+1)*(x-vf)**2
    f4 = -sp.Rational(1, 8)
    f3 = (2*vf+c-1)/4
    f2 = ((c-1)*(1-2*vf)-vf*vf)/2
    f1 = (12*c**3-4*c*c-5*c-1)/(16*c*c)
    # The constant term in the Chebyshev basis is fixed by calibration.
    f0 = rf*(f1+f2+f3+f4)
    check('first-window full certificate', Qf-f0-f1*T(1)-f2*T(2)-f3*T(3)-f4*T(4))

    r3 = (1-2*c*c)/(3+2*c-4*c*c)
    p3 = (-r3-v0)/(c-v0)
    m4 = p3*sp.chebyshevt(4, c)+(1-p3)*sp.chebyshevt(4, v0)
    den = (1+2*c)*(3+2*c-4*c*c)
    check('three-frequency continuation upper slack', m4-r3+2*P/den)
    check('three-frequency continuation lower slack',
          m4+r3-2*(c-1)*(3*c+2)*(4*c*c+2*c-1)/den)

    rg = 1/(R-1+X)
    mg = -1+2*rg*(R-1)/(1+X)
    check('general next-moment formula',
          mg-(R-1-R*X-X*X)/((R-1+X)*(1+X)))
    check('general lower slack', mg+rg-(R+X)*(1-X)/((R-1+X)*(1+X)))
    check('general upper slack',
          mg-rg-(R-2-(R+1)*X-X*X)/((R-1+X)*(1+X)))
    rr = sp.symbols('rho')
    check('signed moment ceiling determinant',
          (1+rr)*(1-(R-2)*rr)-2*(R-1)*rr*rr
          -(1-(R-3)*rr-(3*R-4)*rr*rr))
    check('transition annihilator coefficient identity',
          (1+X)*(R+X)-2*(R-1)-(X*X+(R+1)*X-(R-2)))
    x4 = 2*c*(1+c)/(1-2*c*c)
    check('cutoff-four general transition specialization',
          (x4*x4+5*x4-2)*(1-2*c*c)**2-2*P)

    # Verify the nested radical through its two quadratic relations. Avoid
    # a costly unconstrained simplification of the quartic at a nested root.
    U, V = sp.symbols('U V')
    cc, xi = (V-1)/(U-3), (U-5)/2
    numerator = sp.together(2*(1+xi)*cc*cc+2*cc-xi).as_numer_denom()[0]
    basis = sp.groebner([U*U-33, V*V-25+4*U], V, U)
    assert basis.reduce(numerator)[1] == 0
    checks.append('nested radical by exact quadratic reduction')
    return checks


def measure_checks() -> dict:
    transitions = [pi/5, 2*pi/5, A_STAR, 3*pi/5, 5*pi/7, 4*pi/5]
    samples = list(np.linspace(.01*pi, .999*pi, 251))
    for a in transitions:
        samples.extend([a-1e-7, a, a+1e-7])
    samples.extend([pi/2, pi])
    max_error = 0.0
    minimum_mass = 1.0
    for a in sorted(set(samples)):
        nodes, masses = extremizer(float(a))
        rho = frontier(float(a))
        moments = chebvander(nodes, 4)[:, 1:].T @ masses
        error = abs(float(np.max(np.abs(moments)))-rho)
        assert abs(float(np.sum(masses))-1) < 2e-11
        assert float(np.min(masses)) > -2e-11
        assert float(np.max(nodes)) <= cos(a)+2e-11
        assert error < 2e-10, (a/pi, nodes, masses, moments, rho, error)
        max_error = max(max_error, error)
        minimum_mass = min(minimum_mass, float(np.min(masses)))
    return {'sample_count': len(set(samples)), 'maximum_moment_error': max_error,
            'smallest_mass_including_roundoff': minimum_mass}


def continuation_checks() -> dict:
    cases = []
    for R in [3, 4, 5, 6, 8, 12, 20, 32]:
        xi = (sqrt((R-1)*(R+7))-R-1)/2
        start, stop = 2*pi/(R+1), 2*pi/R
        Xfun = lambda a: -tan(R*a/2)/tan(a/2)
        endpoint = brentq(lambda a: Xfun(a)-xi, start, stop, xtol=1e-14)
        for fraction in [0., .25, .5, .75, 1., 1.5]:
            a = (start+fraction*(endpoint-start) if fraction <= 1
                 else (endpoint+stop)/2)
            X = Xfun(a)
            S = R+X
            rho = 1/(S-1)
            t = a/2
            w = np.array([(1-cos((j-(R-2)/2)*a)/cos(R*t))/S
                          for j in range(R-1)])
            annihilator = np.convolve(w, np.array([1., -2*cos(a), 1.]))
            zeros = np.roots(annihilator[::-1])
            modulus_error = float(np.max(np.abs(np.abs(zeros)-1)))
            assert modulus_error < 2e-8
            z = np.exp(1j*np.angle(zeros))
            V = np.array([z**(-j) for j in range(R)])
            masses = np.linalg.solve(V, np.r_[1., -rho*np.ones(R-1)])
            assert np.max(np.abs(masses.imag)) < 2e-8
            assert np.min(masses.real) > -2e-8
            actual = np.dot(masses, z**(-R))
            predicted = -1+2*rho*(R-1)/(1+X)
            error = abs(actual-predicted)
            assert error < 3e-8
            if fraction <= 1:
                assert abs(actual) <= rho+3e-8
            else:
                assert actual.real > rho
            cases.append({'R': R, 'a_over_pi': a/pi,
                          'position': fraction, 'X': X,
                          'predicted_next_moment': predicted,
                          'observed_next_moment_real': float(actual.real),
                          'moment_error': float(error),
                          'root_modulus_error': modulus_error})
        kappa = 2/(R-3+sqrt((R-1)*(R+7)))
        for rho, expected in [(kappa, 'boundary'), (kappa+1e-5, 'outside')]:
            M = np.full((R+1, R+1), -rho)
            np.fill_diagonal(M, 1)
            M[0, R] = M[R, 0] = rho
            least = float(np.linalg.eigvalsh(M)[0])
            if expected == 'boundary':
                assert abs(least) < 2e-12
                coeff = np.ones(R+1)
                coeff[0] = coeff[-1] = kappa*(R-1)/(1+kappa)
                assert np.max(np.abs(M@coeff)) < 2e-12
            else:
                assert least < -1e-6
    asymptotics = []
    for R in [32, 64, 128, 256]:
        xi = (sqrt((R-1)*(R+7))-R-1)/2
        start, stop = 2*pi/(R+1), 2*pi/R
        endpoint = brentq(lambda a: -tan(R*a/2)/tan(a/2)-xi,
                          start, stop, xtol=2e-16)
        kappa = 2/(R-3+sqrt((R-1)*(R+7)))
        asymptotics.append({'R': R, 'scaled_width': R**3*(endpoint-start),
                            'width_limit': 8*pi,
                            'scaled_height_excess': R**3*(kappa-1/R),
                            'height_limit': 4.})
    return {'sample_count': len(cases),
            'maximum_next_moment_error': max(z['moment_error'] for z in cases),
            'signed_moment_matrix_cases': 16,
            'cases': cases, 'asymptotic_diagnostics': asymptotics}


def lp_checks(grid_size: int, case_count: int) -> dict:
    radii = set(np.linspace(.025, .995, case_count))
    radii.update([.2, .4, A_STAR/pi, .5, .6, 5/7, .8])
    rows = []
    for fraction in sorted(radii):
        a = pi*float(fraction)
        grid = np.linspace(-1., cos(a), grid_size)
        T = chebvander(grid, 4)[:, 1:].T
        A = np.column_stack([np.vstack([T, -T]), -np.ones(8)])
        result = linprog(np.r_[np.zeros(grid_size), 1.], A_ub=A,
                         b_ub=np.zeros(8),
                         A_eq=np.array([np.r_[np.ones(grid_size), 0.]]),
                         b_eq=[1.], bounds=[(0., None)]*(grid_size+1),
                         method='highs')
        assert result.success, result.message
        rho = frontier(a)
        excess = float(result.fun-rho)
        tolerance = max(3e-6, 50./(grid_size-1)**2)
        assert -2e-7 <= excess <= tolerance, (fraction, rho, result.fun, excess)
        rows.append({'a_over_pi': float(fraction), 'analytic': rho,
                     'discrete_lp': float(result.fun), 'excess': excess})
    return {'cosine_grid_points': grid_size, 'case_count': len(rows),
            'maximum_discretization_excess': max(row['excess'] for row in rows),
            'rows': rows}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Write JSON here; otherwise use stdout.')
    parser.add_argument('--skip-lp', action='store_true', help='Skip the optional grid LP sweep.')
    parser.add_argument('--lp-grid', type=int, default=10001)
    parser.add_argument('--lp-cases', type=int, default=57)
    args = parser.parse_args()
    if args.lp_grid < 1001 or args.lp_cases < 5:
        parser.error('Use at least 1001 grid points and 5 LP cases.')
    result = {
        'scope': ('Exact algebraic identity certificates and finite numerical diagnostics; '
                  'the article supplies the continuum proofs.'),
        'transition_c': C_STAR, 'transition_a_over_pi': A_STAR/pi,
        'transition_value': frontier(A_STAR),
        'symbolic_identities': exact_checks(),
        'extremizer_checks': measure_checks(),
        'general_continuation_checks': continuation_checks(),
    }
    if not args.skip_lp:
        result['finite_grid_lp_checks'] = lp_checks(args.lp_grid, args.lp_cases)
    output = json.dumps(result, indent=2, sort_keys=True)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output)
        print(f'PASS: {len(result["symbolic_identities"])} exact identities; '
              f'{result["extremizer_checks"]["sample_count"]} extremizer checks; '
              f'{result["general_continuation_checks"]["sample_count"]} continuation checks; '
              f'{result.get("finite_grid_lp_checks", {}).get("case_count", 0)} LP cases.')
        print(args.output)
    else:
        print(output, end='')


if __name__ == '__main__':
    main()
