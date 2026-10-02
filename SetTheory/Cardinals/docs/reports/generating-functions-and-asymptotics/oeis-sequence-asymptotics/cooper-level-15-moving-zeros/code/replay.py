#!/usr/bin/env python3
"""Finite exact-algebra and high-precision checks for the accompanying article.

This replay does not infer asymptotic theorems from numerical samples. The
article proves the remainders; this program tests the formulas and selected
finite evaluations. All input files are local. No network access is used.
"""
from __future__ import annotations
import argparse, json, math, platform, time
from pathlib import Path
import mpmath as mp
import sympy as s
from coefficients_primary import CASES, coeffs, x
from coefficients_auxiliary import G14, H14, G15, H15, e, get

HERE = Path(__file__).resolve().parent
EXPECTED = json.loads((HERE / 'expected_coefficients.json').read_text())
mp.mp.dps = 100


def number(z):
    z = s.sympify(z)
    return mp.mpc(str(s.N(s.re(z), 105)), str(s.N(s.im(z), 105)))


def shown(z, digits=28):
    return mp.nstr(z, digits)


def small(a, b, tol=mp.mpf('1e-75')):
    error = abs(a-b)/max(1, abs(a), abs(b))
    assert error < tol, (shown(error), shown(a), shown(b))
    return shown(error, 8)


def exact_equal(a, b):
    assert s.simplify(a-b) == 0, (a, b)


R11 = mp.findroot(lambda r: 1-20*r+56*r*r-44*r**3, mp.mpf('.06'))
PRIMARY_ROOTS = {'11': R11, '14A': 1/(5+4*mp.sqrt(2)),
                 '14B': 1/(9+4*mp.sqrt(2)), '15A': mp.mpf(1)/12,
                 '24': mp.mpf(1)/8}
AUXILIARY = [
    ('14C', G14, H14, 4*s.sqrt(2), 8*s.sqrt(2),
     8*s.sqrt((8*s.sqrt(2)-11)/7), s.QQ.algebraic_field(s.sqrt(2)), 14),
    ('14barC', G14, H14, -4*s.sqrt(2), -9-4*s.sqrt(2),
     (9+4*s.sqrt(2))**s.Rational(3, 2)/(2*s.sqrt(7)),
     s.QQ.algebraic_field(s.sqrt(2)), 28),
    ('15B', G15, H15, -11, -s.Integer(12), 12*s.sqrt(3), s.QQ, 60),
    ('15C', G15, H15, 2*s.I, 11+2*s.I,
     (11+2*s.I)**s.Rational(3, 2)/20, s.QQ_I, None),
    ('15barC', G15, H15, -2*s.I, 11-2*s.I,
     (11-2*s.I)**s.Rational(3, 2)/20, s.QQ_I, None),
]


def exact_coefficient_checks():
    data = {}
    for name, (N, G, H, P) in CASES.items():
        bs = coeffs(name, 6)
        for a, b in zip(bs, EXPECTED['fixed'][name]):
            exact_equal(a, s.sympify(b))
        data[name] = {'G': G, 'H': H, 'r': PRIMARY_ROOTS[name],
                      'b': [number(z.subs(x, s.Float(str(PRIMARY_ROOTS[name]), 110))) for z in bs]}
        r = data[name]['r']
        D = number(s.diff(G, x).subs(x, s.Float(str(r), 110)))
        data[name]['C'] = mp.sqrt(N)/(2*mp.pi**mp.mpf('1.5')*mp.sqrt(-r*D))
    for name, GG, HH, ep, R, Cpi, K, mu2 in AUXILIARY:
        G, H = s.expand(GG.subs(e, ep)), s.expand(HH.subs(e, ep))
        r = s.expand_complex(1/R)
        bs = get(G, H, r, K, 6)
        for a, b in zip(bs, EXPECTED['fixed'][name]):
            exact_equal(a, s.sympify(b))
        if mu2 is not None:
            exact_equal(mu2/(4*(-r*s.diff(G, x).subs(x, r))), Cpi*Cpi)
        data[name] = {'G': G, 'H': H, 'r': number(r), 'b': list(map(number, bs)),
                      'C': number(Cpi)/mp.pi**mp.mpf('1.5')}
    # Both earlier algebraic descriptions of the level-11 amplitude.
    r = x
    G = 1-20*r+56*r*r-44*r**3
    c2 = 11/(4*(-r*s.diff(G, r)))
    for expression in (-1331-1020*c2-1936*c2*c2+704*c2**3,
                       11264*(r*r*c2)**3+928*(r*r*c2)-11):
        numerator = s.together(expression).as_numer_denom()[0]
        assert s.rem(numerator, G, r) == 0
    # The Gaussian amplitudes use the principal powers on Re(R)>0.
    exact_equal(6*s.sqrt(3)/(5*12**s.Rational(3, 2)), s.Rational(1, 20))
    return data


def recurrence_values(G, H, nmax):
    g, h = s.Poly(G, x), s.Poly(H, x)
    gs = [number(g.nth(j)) for j in range(g.degree()+1)]
    hs = [number(h.nth(j)) for j in range(g.degree()+1)]
    values = [mp.mpf(1)]
    for n in range(1, nmax+1):
        z = sum((n*gs[j]*(n-mp.mpf(j)/2)*(n-j)
                 -2*hs[j]*(n-mp.mpf(j)/2))*values[n-j]
                for j in range(1, min(n, len(gs)-1)+1))
        values.append(-z/n**3)
    return values


def fixed_case_checks(data):
    summary = {}
    for name, row in data.items():
        values = recurrence_values(row['G'], row['H'], 2000)
        R, C, bs = 1/row['r'], row['C'], row['b']
        checks = []
        for n in (500, 1000, 2000):
            normalized = values[n]*mp.mpf(n)**mp.mpf('1.5')/R**n/C
            scaled = []
            for K in range(5):
                approximation = sum(bs[j]/mp.mpf(n)**j for j in range(K+1))
                error = (normalized-approximation)*mp.mpf(n)**(K+1)
                # A finite check at this exact sample, not an all-n error bound.
                assert abs(error) < 10*(1+abs(bs[K+1])), (name, n, K)
                scaled.append(shown(error, 18))
            checks.append({'n': n, 'scaled_remainders_K0_to_4': scaled})
        summary[name] = {'R': shown(R), 'C': shown(C), 'checks': checks}
    return summary


def eta(tau):
    q = mp.exp(2*mp.pi*1j*tau)
    return mp.exp(mp.pi*1j*tau/12)*mp.qp(q)


def eta_pair(N, tau):
    z = lambda d: eta(d*tau)
    if N == 14:
        return (z(1)*z(14)/(z(2)*z(7)))**4, z(1)*z(2)*z(7)*z(14)
    return (z(3)*z(15)/(z(1)*z(5)))**2, z(1)*z(3)*z(5)*z(15)


def mobius(A, tau):
    a, b, c, d = (map(int,A) if isinstance(tau,(mp.mpf,mp.mpc)) else A)
    return (a*tau+b)/(c*tau+d)


def connection_checks():
    A = s.Matrix([[2, 1], [1, 6]])
    U = s.Matrix([[0, 1], [-1, 0]])
    assert U.T*A*U == 11*A.inv()
    gamma14 = s.Matrix([[7, -4], [14, -7]])
    gamma15 = s.Matrix([[15, -8], [30, -15]])
    assert gamma14.det() == 7 and gamma15.det() == 15
    assert s.Matrix([[8, 1], [15, 2]])*s.Matrix([[0, -1], [15, 0]]) == gamma15
    tau = s.symbols('tau')
    eta_rows = [(1, 7, [1, -4, 2, -7], -s.Rational(1, 2)),
                (7, 1, [7, -4, 2, -1], s.Integer(0)),
                (2, 14, [1, -8, 1, -7], -s.Rational(3, 4)),
                (14, 2, [7, -8, 1, -1], s.Rational(1, 4))]
    for d, argument, M, phase in eta_rows:
        a, b, c, dd = M
        assert a*dd-b*c == 1
        exact_equal(d*mobius(list(gamma14), tau), mobius(M, argument*tau))
        # For c=1,2 every summand in this Dedekind sum vanishes.
        dedekind = sum((s.Rational(k, c)-s.Rational(1, 2))
                      *(s.Rational((dd*k) % c, c)-s.Rational(1, 2))
                      for k in range(1, c))
        exact_equal((s.Rational(a+dd, 12*c)-dedekind-s.Rational(1, 4)), phase)
    assert sum(row[3] for row in eta_rows) == -1
    # Eta-quotient congruences and character squares for P15,w15.
    for exponents in ({1: 1, 3: 1, 5: 1, 15: 1}, {1: -2, 3: 2, 5: -2, 15: 2}):
        assert sum(d*v for d, v in exponents.items()) % 24 == 0
        assert sum((15//d)*v for d, v in exponents.items()) % 24 == 0
    results = []
    for tau in (mp.mpc('.23', '.41'), mp.mpc('.51', '.6'), mp.mpc('-.17', '.8')):
        w, p = eta_pair(14, tau)
        wg, pg = eta_pair(14, mobius(list(gamma14), tau))
        results.append({'case': '14W7', 'tau': shown(tau),
                        'w_error': small(wg, 1/w),
                        'P_error': small(pg, -(14*tau-7)**2*p/7)})
        w, p = eta_pair(15, tau)
        wg, pg = eta_pair(15, mobius(list(gamma15), tau))
        X, Xg = w/(1-3*w)**2, wg/(1-3*wg)**2
        results.append({'case': '15B', 'tau': shown(tau),
                        'X_error': small(Xg, X),
                        'Z_error': small(pg/Xg, -(30*tau-15)**2*(p/X)/15)})
    for N, D in ((14, 7), (15, 15)):
        y = 1/(2*mp.sqrt(D))
        def functions(y):
            w, p = eta_pair(N, mp.mpf('.5')+1j*y)
            if N == 14:
                ep = -4*mp.sqrt(2)
                X = w/(1+(ep-7)*w+w*w)
            else:
                X = w/(1-3*w)**2
            return X, p/X
        X, Z = functions(y)
        r = -1/(9+4*mp.sqrt(2)) if N == 14 else -mp.mpf(1)/12
        results.append({'case': f'{N}_endpoint', 'r_error': small(X, r),
                        'log_derivative_error': small(mp.diff(lambda t: functions(t)[1], y)/Z,
                                                      -2*mp.sqrt(D))})
    return results


def convolve(a, b, K):
    return [s.expand(sum(a[j]*b[k-j] for j in range(k+1))) for k in range(K+1)]


def appell_checks():
    # Independently form the first twelve polynomials from Cooper's recurrence.
    a = [s.Integer(1)]
    for n in range(12):
        value = (2*n+1)*((2*e+5)*(n*n+n)+e+2)*a[n]
        if n >= 1:
            value -= n*((6*e*e+30*e-7)*n*n+e*e+4*e-1)*a[n-1]
        if n >= 2:
            value += n*(2*n-1)*(n-1)*(2*e**3+15*e*e-7*e+20)*a[n-2]
        if n >= 3:
            value -= n*(n-1)*(n-2)*(e-1)*(e+11)*(e*e+4)*a[n-3]
        a.append(s.expand(value/(n+1)**3))
        exact_equal(s.diff(a[-1],e), (n+1)*a[-2])
        assert s.Poly(a[-1],e).LC() == 1
    assert [v.subs(e,1) for v in a[:8]] == [1,3,15,105,855,7533,69909,673515]
    return {'exact_Appell_identity_checked_through_degree':12}


def crossover_algebra():
    u, U = s.symbols('u U')
    P = {}
    for sigma in (1, -1):
        r = 1/(e+11) if sigma == 1 else 1/(e-1)
        bs = get(G15, H15, r, s.QQ.frac_field(e), 3)
        for a, b in zip(bs, EXPECTED['crossover'][str(sigma)]['b0to3']):
            exact_equal(a, s.sympify(b))
        E = [0]+[(-1)**k*(sigma*u/6)**(k+1)/(k+1)
                 +s.Rational(3, 2)*(-1)**(k+1)*(sigma*u/6)**k/k for k in range(1, 4)]
        exponential = [s.Integer(1)]
        for k in range(1, 4):
            exponential.append(s.expand(sum(j*E[j]*exponential[k-j] for j in range(1, k+1))/k))
        B = [s.expand(sum(s.diff(bs[m], e, k-m).subs(e, -5)*u**(k-m)/s.factorial(k-m)
                         for m in range(k+1))) for k in range(4)]
        P[sigma] = convolve(exponential, B, 3)
        for a, b in zip(P[sigma], EXPECTED['crossover'][str(sigma)]['P0to3']):
            exact_equal(a, s.sympify(b))
    root = [s.Integer(0)]*4
    for order in range(1, 4):
        powers = [[s.Integer(1)]+[s.Integer(0)]*3]
        for m in range(1, 4):
            powers.append(convolve(powers[-1], root, 3))
        composed = {}
        for sigma in (1, -1):
            a = [s.Integer(0)]*4
            for j in range(4):
                for m in range(4-j):
                    derivative = s.diff(P[sigma][j], u, m).subs(u, U)/s.factorial(m)
                    for k in range(4-j):
                        a[j+k] += derivative*powers[m][k]
            composed[sigma] = list(map(s.expand, a))
        exponential = [s.Integer(1)]
        for k in range(1, 4):
            exponential.append(s.expand(sum(j*root[j]/3*exponential[k-j]
                                             for j in range(1, k+1))/k))
        known = s.expand(convolve(exponential, composed[1], 3)[order]-composed[-1][order])
        root[order] = s.factor(-3*known)
    for a, b in zip(root[1:], EXPECTED['crossover']['zero_u_coefficients_in_U']):
        exact_equal(a, s.sympify(b))
    return P, root[1:]


def level15(epsilon, N):
    a = [mp.mpf(1)]
    z = epsilon
    for n in range(N):
        b = (2*n+1)*((2*z+5)*(n*n+n)+z+2)*a[n]
        if n >= 1:
            b -= n*((6*z*z+30*z-7)*n*n+z*z+4*z-1)*a[n-1]
        if n >= 2:
            b += n*(2*n-1)*(n-1)*(2*z**3+15*z*z-7*z+20)*a[n-2]
        if n >= 3:
            b -= n*(n-1)*(n-2)*(z-1)*(z+11)*(z*z+4)*a[n-3]
        a.append(b/(n+1)**3)
    return a[-1]


def crossover_numerics(P, root_coefficients):
    u, U = s.symbols('u U')
    polys = {sigma: [s.lambdify(u, p, 'mpmath') for p in ps] for sigma, ps in P.items()}
    A = mp.mpf(6)**mp.mpf('1.5')/(20*mp.pi**mp.mpf('1.5'))
    def normalized(v, n):
        return level15(-5+v/n, n)/(A*mp.mpf(6)**n/mp.mpf(n)**mp.mpf('1.5'))
    u0 = 3*mp.log(10)
    roots = [mp.re(number(a.subs(U, 3*s.log(10)))) for a in root_coefficients]
    checks = []
    for v in (mp.mpf(0), mp.mpf(3), u0, mp.mpc(2, 3)):
        for n in (199, 200, 499, 500):
            predicted = mp.exp(v/6)*sum(polys[1][j](v)/mp.mpf(n)**j for j in range(4))
            predicted += 10*(-1)**n*mp.exp(-v/6)*sum(polys[-1][j](v)/mp.mpf(n)**j for j in range(4))
            scaled = (normalized(v, n)-predicted)*mp.mpf(n)**4
            assert abs(scaled) < 100000, (v, n, scaled)
            checks.append({'u': shown(v), 'n': n, 'scaled_order3_remainder': shown(scaled, 18)})
    zeros = []
    for n in (199, 399, 799):
        zero = mp.findroot(lambda v: normalized(v, n), (u0, u0+mp.mpf('.1')),
                           tol=mp.mpf('1e-80'))
        assert abs(zero-u0) < mp.mpf('.1')
        assert abs(normalized(zero, n)) < mp.mpf('1e-75')
        predicted = u0+sum(roots[j-1]/mp.mpf(n)**j for j in range(1, 4))
        remainder = (zero-predicted)*mp.mpf(n)**4
        assert abs(remainder) < 100000
        zeros.append({'n': n, 'epsilon_zero': shown(-5+zero/n, 45),
                      'scaled_after_u3_remainder': shown(remainder, 20),
                      'normalized_residual': shown(normalized(zero, n), 8)})
    complex_zeros = []
    for n, imaginary in ((399,6*mp.pi),(400,3*mp.pi)):
        U0 = u0+1j*imaginary
        zero = mp.findroot(lambda v: normalized(v,n),(U0,U0+mp.mpf('.1')),
                           tol=mp.mpf('1e-80'))
        assert abs(zero-U0) < mp.mpf('.2')
        assert abs(normalized(zero,n)) < mp.mpf('1e-75')
        u_corrections = [s.lambdify(U,a,'mpmath')(U0) for a in root_coefficients]
        predicted = U0+sum(u_corrections[j-1]/mp.mpf(n)**j for j in range(1,4))
        remainder = (zero-predicted)*mp.mpf(n)**4
        assert abs(remainder) < 10000000
        complex_zeros.append({'n':n,'limiting_U':shown(U0),
                              'epsilon_zero':shown(-5+zero/n,40),
                              'scaled_after_u3_remainder':shown(remainder,20),
                              'normalized_residual':shown(normalized(zero,n),8)})
    return {'complex_u_checks': checks, 'odd_zero_checks': zeros,
            'fixed_complex_zero_checks':complex_zeros}


INTEGER_PARAMETERS = {'11': (10, 4, -56, -8, 22), '14A': (3, 1, 47, 4, 14),
                      '14B': (11, 5, -121, -20, 98), '15A': (7, 3, -29, -4, 30),
                      '24': (4, 2, 16, 4, -64)}


def integer_values(name, N):
    a, b, c, d, e = INTEGER_PARAMETERS[name]
    values = [1]
    for n in range(N):
        v = (2*n+1)*(a*n*n+a*n+b)*values[n]
        if n >= 1:
            v += n*(c*n*n+d)*values[n-1]
        if n >= 2:
            v += e*n*(2*n-1)*(n-1)*values[n-2]
        assert v % (n+1)**3 == 0
        values.append(v//(n+1)**3)
    assert all(a <= b for a, b in zip(values, values[1:]))
    return values


def inverse_checks(data):
    results = []
    for name in INTEGER_PARAMETERS:
        values = integer_values(name, 501)
        row = data[name]
        C, lam = mp.re(row['C']), mp.log(mp.re(1/row['r']))
        bs = list(map(mp.re, row['b']))
        for n in (100, 500):
            # Exact integer target strictly between consecutive exact terms.
            M = math.isqrt(values[n]*values[n+1])
            assert values[n] < M < values[n+1]
            L = mp.log(M/C)
            v = L/lam
            for _ in range(6):
                S = sum(bs[j]/v**j for j in range(5))
                v = (L+mp.mpf('1.5')*mp.log(v)-mp.log(S))/lam
            assert int(mp.ceil(v)) == n+1
            results.append({'case': name, 'n': n, 'target_digits': len(str(M)),
                            'inverse_minus_n': shown(v-n),
                            'threshold_verified_by_exact_neighbors': n+1})
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('replay_results.json'))
    args = parser.parse_args()
    started = time.monotonic()
    data = exact_coefficient_checks()
    print('Exact coefficients through order6 and amplitude identities: PASS', flush=True)
    fixed = fixed_case_checks(data)
    print('All ten finite recurrence/asymptotic sample checks: PASS', flush=True)
    connections = connection_checks()
    print('Exact eta phases/matrices and numerical connection checks: PASS', flush=True)
    appell = appell_checks()
    P, root = crossover_algebra()
    print('Exact crossover polynomials and zero coefficients through order3: PASS', flush=True)
    crossover = crossover_numerics(P, root)
    print('Complex-u additive examples and moving odd-index roots: PASS', flush=True)
    inverse = inverse_checks(data)
    print('Inverse examples with exact integer-neighbor verification: PASS', flush=True)
    result = {'status': 'PASS', 'python': platform.python_version(),
              'sympy': s.__version__, 'mpmath': mp.__version__, 'decimal_precision': mp.mp.dps,
              'scope': 'Exact algebra and stated finite numerical checks; analytic error proofs are in the article.',
              'fixed_cases': fixed, 'connection_checks': connections,
              'crossover': crossover, 'Appell_checks': appell, 'inverse_checks': inverse}
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(f'Wrote {args.output}; elapsed {time.monotonic()-started:.1f}s', flush=True)


if __name__ == '__main__':
    main()
