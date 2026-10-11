#!/usr/bin/env python3
"""Replay the centered harmonic-power identities.

Exact checks use rational symbolic algebra. Numerical checks use the
original series with independent Euler--Maclaurin/Hurwitz subtraction;
truncation stability is diagnostic, not a rigorous error enclosure.
Requires sympy and mpmath. Writes results/harmonic_powers.json.
"""
from pathlib import Path
from functools import lru_cache
import json
import math
import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
u, k = sp.symbols('u k')


def exact_rows():
    """Coefficients of Q, B, and sum u^(k+1) E_k/(k+1)!."""
    G = [(sp.S.One, sp.S.Zero, sp.S.Zero)]
    for m in range(1, 5):
        acc = [sp.S.Zero, u**(m+1)/sp.factorial(m+2),
               -u**m/sp.prod(k+i for i in range(2, m+2))]
        for j in range(m):
            a = ((-1)**(m+1-j)*sp.binomial(m+1, j)
                 - u**(m+1-j)/sp.factorial(m+1-j))
            for q in range(3):
                acc[q] += a*G[j][q]
        G.append(tuple(sp.factor(x/(u+m+1)) for x in acc))

    def row(r):
        ans = [sp.factor(sum(sp.binomial(2*r, j)*(-sp.Rational(1, 2))**(2*r-j)
                             *G[j][q] for j in range(2*r+1))) for q in range(3)]
        # B = 1 + sum u^k E_k/k!, so use Q, 1, and the same E basis.
        ans[2] = sp.factor(ans[2] + (k+1)*ans[1]/u)
        return ans

    V, W = row(1), row(2)
    target_V = [
        (u**3-3*u-3)/(12*(u+3)), -u**3/(24*(u+3)),
        -(k-1)*(k+1)*(k+6)*u**2/(24*(u+3)*(k+2)*(k+3))]
    R = u**3+18*u**2+90*u+150
    S = u**3+6*u**2+15*u+15
    target_W = [-R*x/(60*(u+5)) for x in V]
    target_W[0] -= S/(240*(u+5))
    target_W[2] += k*(k-1)*(k+1)*u**4/(120*(u+5)*sp.prod(k+i for i in range(2, 6)))
    residuals = [sp.factor(x-y) for x, y in zip(V, target_V)]
    residuals += [sp.factor(x-y) for x, y in zip(W, target_W)]
    assert residuals == [0]*6
    q_identity = ((k+1)/(2*sp.factorial(k+1))
                  - 1/sp.factorial(k+1) - (k-1)/(2*sp.factorial(k+1)))
    assert sp.simplify(q_identity) == 0
    return {'symbolic_generator_residuals': [str(x) for x in residuals],
            'Q_row_residual': str(sp.simplify(q_identity))}


def exact_small_values():
    z = {j: sp.Symbol(f'zeta_{j}') for j in range(2, 6)}
    E = {(0, j): z[j] for j in range(2, 6)}
    E[1, 2] = z[3]
    E[1, 3] = z[4]/4
    E[2, 2] = sp.Rational(11, 4)*z[4]
    Q = [sp.S.Zero, sp.Rational(1, 2)]
    for p in range(2, 6):
        Q.append(sp.expand(-p*Q[-1] + sum(
            sp.Rational(j-1, 2)*sp.binomial(p, j+1)*E[p-j-1, j]
            for j in range(2, p))))
    V = [sp.S.Zero]
    for p in range(1, 6):
        a = -p*V[p-1] - Q[p]/4 - p*Q[p-1]/4
        if p >= 3:
            a += sp.factorial(p)/sp.factorial(p-3)*Q[p-3]/12
        if p == 3:
            a -= sp.Rational(1, 4)
        for j in range(2, p-2):
            a -= sp.Rational((j-1)*(j+1)*(j+6), 24)*sp.binomial(p, j+3)*E[p-j-3, j]
        V.append(sp.expand(a/3))
    W = [sp.S.Zero]
    for p in range(1, 6):
        a = -p*W[p-1]
        for j, coefficient in enumerate([150, 90, 18, 1]):
            if p >= j:
                a -= sp.Rational(coefficient, 60)*sp.factorial(p)/sp.factorial(p-j)*V[p-j]
        for j, coefficient in enumerate([15, 15, 6, 1]):
            if p >= j:
                a -= sp.Rational(coefficient, 240)*sp.factorial(p)/sp.factorial(p-j)*Q[p-j]
        for j in range(2, p-4):
            a += sp.Rational(j*(j-1)*(j+1), 120)*sp.binomial(p, j+5)*E[p-j-5, j]
        W.append(sp.expand(a/5))
    expected_v5 = (-sp.Rational(200, 81)-sp.Rational(23, 54)*z[2]
                   +sp.Rational(5, 12)*z[3]-sp.Rational(11, 8)*z[4])
    expected_w = [sp.S.Zero, sp.Rational(7, 480), sp.Rational(19, 3600),
        sp.Rational(493, 18000)+sp.Rational(7, 480)*z[2],
        -sp.Rational(6479, 67500)+sp.Rational(19, 1800)*z[2]+sp.Rational(7, 80)*z[3],
        sp.Rational(98437, 202500)+sp.Rational(643, 5400)*z[2]
        +sp.Rational(19, 240)*z[3]+sp.Rational(77, 160)*z[4]]
    assert sp.expand(V[5]-expected_v5) == 0
    assert [sp.expand(a-b) for a, b in zip(W, expected_w)] == [0]*6
    return [Q, V, W], z


def exact_bernoulli(max_r=12):
    # Up to degree two in u, all E_k contributions vanish.
    trunc = lambda x: sp.series(x, u, 0, 3).removeO().expand()
    G = []
    for m in range(2*max_r+1):
        a = u**(m+1)/sp.factorial(m+2)
        for j in range(m):
            c = ((-1)**(m+1-j)*sp.binomial(m+1, j)
                 -u**(m+1-j)/sp.factorial(m+1-j))
            a += trunc(c*G[j])
        G.append(trunc(a/(u+m+1)))
    rows = []
    for r in range(max_r+1):
        a = sp.expand(sum(sp.binomial(2*r, j)*(-sp.Rational(1, 2))**(2*r-j)
                          *G[j] for j in range(2*r+1)))
        first = sp.bernoulli(2*r, sp.Rational(1, 2))/2
        second = -sum(sp.binomial(2*r, 2*j)*sp.bernoulli(2*j)
                      *sp.bernoulli(2*r-2*j, sp.Rational(1, 2))/sp.Integer(2*j+1)
                      for j in range(r+1))
        assert sp.expand(a).coeff(u, 1) == first
        assert 2*sp.expand(a).coeff(u, 2) == second
        rows.append({'r': r, 'first_power': str(first), 'second_power': str(second)})
    return rows


def convolution(a, b, J):
    return [sum(a[j]*b[n-j] for j in range(n+1)) for n in range(J+1)]


def centered_bernoulli(j):
    return (mp.power(2, 1-2*j)-1)*mp.bernoulli(2*j)


@lru_cache(None)
def hurwitz_derivative(s, a_string, q):
    return mp.zeta(s, mp.mpf(a_string), derivative=q)


def independent_raw_value(p, r, N, J):
    """Analytic continuation using the centered asymptotic series, not G_m."""
    b = [mp.euler]+[-centered_bernoulli(j)/(2*j) for j in range(1, J+1)]
    powers = [[mp.mpf(1)]+[mp.mpf(0)]*J]
    for _ in range(p):
        powers.append(convolution(powers[-1], b, J))
    value, h = mp.mpf(0), mp.mpf(0)
    for n in range(N):
        if n:
            h += mp.mpf(1)/n
        value += (n+mp.mpf('.5'))**(2*r)*h**p
    a_string = str(N+mp.mpf('.5'))
    for j in range(J+1):
        for q in range(p+1):
            coefficient = mp.binomial(p, q)*powers[p-q][j]
            if coefficient:
                value += coefficient*(-1)**q*hurwitz_derivative(2*j-2*r, a_string, q)
    return value


def exponential_coefficients(argument, b):
    result = [mp.mpf(1)]
    for n in range(1, len(b)):
        result.append(argument*sum(j*b[j]*result[n-j] for j in range(1, n+1))/n)
    return result


def independent_exponent_moment(r, argument, N=48, J=20):
    b = [mp.mpf(0)]+[-centered_bernoulli(j)/(2*j) for j in range(1, J+1)]
    c = exponential_coefficients(argument, b)
    value, h = mp.mpf(0), mp.mpf(0)
    for n in range(N):
        if n:
            h += mp.mpf(1)/n
        value += (n+mp.mpf('.5'))**(2*r)*mp.exp(argument*h)
    value += mp.exp(mp.euler*argument)*sum(c[j]*mp.zeta(-2*r-argument+2*j, N+mp.mpf('.5'))
                                             for j in range(J+1))
    return value


def independent_Ek_values(argument, maximum_k=36, N=48, J=40):
    b = [mp.mpf(0), -mp.mpf('.5')]+[mp.mpf(0)]*(J-1)
    for j in range(2, J+1, 2):
        b[j] = -mp.bernoulli(j)/j
    c = exponential_coefficients(argument, b)
    prefix, h = [], mp.mpf(0)
    for n in range(1, N):
        prefix.append((n, mp.exp(argument*h)))
        h += mp.mpf(1)/n
    values = {}
    for j in range(2, maximum_k+1):
        values[j] = sum(v/n**j for n, v in prefix)
        values[j] += mp.exp(mp.euler*argument)*sum(c[l]*mp.zeta(j-argument+l, N)
                                                   for l in range(J+1))
    return values


def numerical_checks(rows, z):
    mp.mp.dps = 65
    records = []
    max_error, max_stability = mp.mpf(0), mp.mpf(0)
    for r in range(3):
        for p in range(1, 6):
            f = sp.lambdify(tuple(z.values()), rows[r][p], 'mpmath')
            exact = f(*(mp.zeta(j) for j in z))
            coarse = independent_raw_value(p, r, 32, 16)
            fine = independent_raw_value(p, r, 48, 20)
            error, stability = abs(fine-exact), abs(fine-coarse)
            assert error < mp.mpf('1e-38')
            assert stability < mp.mpf('1e-28')
            max_error, max_stability = max(max_error, error), max(max_stability, stability)
            records.append({'p': p, 'r': r, 'exact_expression': str(rows[r][p]),
                'value': mp.nstr(fine, 40), 'absolute_diagnostic_error': mp.nstr(error, 8),
                'two_truncation_difference': mp.nstr(stability, 8)})
    generators = []
    for argument in [mp.mpf('.3'), mp.mpf('-.4')]:
        E = independent_Ek_values(argument)
        B = 1+sum(argument**j/mp.factorial(j)*E[j] for j in E)
        G = []
        for m in range(5):
            value = argument**(m+1)*B/mp.factorial(m+2)
            value -= sum(argument**(j+m+1)*E[j]/mp.factorial(j+m+1) for j in E)
            for j in range(m):
                value += (((-1)**(m+1-j)*math.comb(m+1, j)
                           -argument**(m+1-j)/mp.factorial(m+1-j))*G[j])
            G.append(value/(argument+m+1))
        for r in range(3):
            generated = sum(math.comb(2*r, j)*(-mp.mpf('.5'))**(2*r-j)*G[j]
                            for j in range(2*r+1))
            direct = independent_exponent_moment(r, argument)
            error = abs(generated-direct)
            assert error < mp.mpf('1e-36')
            generators.append({'u': str(argument), 'r': r, 'value': mp.nstr(direct, 40),
                               'absolute_diagnostic_error': mp.nstr(error, 8)})
    return {'method': 'Independent centered Euler--Maclaurin and Hurwitz derivatives; omitted tails are not rigorously enclosed.',
            'working_decimal_digits': mp.mp.dps,
            'coarse_truncation': {'prefix_length': 32, 'even_orders': 16},
            'fine_truncation': {'prefix_length': 48, 'even_orders': 20},
            'maximum_absolute_diagnostic_error': mp.nstr(max_error, 8),
            'maximum_two_truncation_difference': mp.nstr(max_stability, 8),
            'centered_values': records, 'full_exponent_generator_checks': generators}



def independent_odd_harmonic_value(q, r, N, J):
    """Original generalized harmonic sums with midpoint Hurwitz subtraction."""
    value, h = mp.mpf(0), mp.mpf(0)
    for n in range(N):
        if n:
            h += mp.mpf(n)**(-q)
        value += (n+mp.mpf('.5'))**(2*r)*h
    a = N+mp.mpf('.5')
    value += mp.zeta(q)*mp.zeta(-2*r, a)
    value -= mp.zeta(q-1-2*r, a)/(q-1)
    for j in range(1, J+1):
        coefficient = centered_bernoulli(j)*mp.rf(q, 2*j-1)/mp.factorial(2*j)
        value -= coefficient*mp.zeta(q-1+2*j-2*r, a)
    return value


def odd_harmonic_checks():
    n, N = sp.symbols('n N', integer=True, nonnegative=True)
    residuals = []
    for r in range(9):
        faulhaber = sum(sp.binomial(2*r+1, 2*j)*sp.bernoulli(2*j, sp.Rational(1, 2))
                        *N**(2*r+1-2*j) for j in range(r+1))/sp.Integer(2*r+1)
        finite_sum = sp.summation((n+sp.Rational(1, 2))**(2*r), (n, 0, N-1))
        residual = sp.expand(faulhaber-finite_sum)
        assert residual == 0
        residuals.append(str(residual))
    records = []
    for q in [3, 5]:
        for r in range(3):
            exact = -sum(mp.binomial(2*r+1, 2*j)*centered_bernoulli(j)
                         *mp.zeta(q-2*r-1+2*j) for j in range(r+1))/(2*r+1)
            # B_0(1/2) = 1; centered_bernoulli(0) also evaluates to 1.
            coarse = independent_odd_harmonic_value(q, r, 32, 16)
            fine = independent_odd_harmonic_value(q, r, 48, 20)
            error, stability = abs(fine-exact), abs(fine-coarse)
            assert error < mp.mpf('1e-36')
            assert stability < mp.mpf('1e-27')
            records.append({'harmonic_order': q, 'r': r, 'value': mp.nstr(fine, 40),
                'absolute_diagnostic_error': mp.nstr(error, 8),
                'two_truncation_difference': mp.nstr(stability, 8)})
    return {'exact_centered_Faulhaber_residuals': residuals,
            'numerical_checks': records,
            'scope': 'Positive odd harmonic orders only; even-order specialization can meet a moving divisor.'}


def main():
    result = {'scope': 'Proof support for the all-r centered harmonic-power generator; numerical results are diagnostics.'}
    result['exact_generators'] = exact_rows()
    rows, z = exact_small_values()
    result['bernoulli_checks'] = exact_bernoulli()
    result['numerical_checks'] = numerical_checks(rows, z)
    result['odd_harmonic_checks'] = odd_harmonic_checks()
    result['all_checks_passed'] = True
    destination = ROOT/'results'/'harmonic_powers.json'
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'all_checks_passed': True,
                      'exact_generator_residuals': 7,
                      'bernoulli_identities_checked': 2*len(result['bernoulli_checks']),
                      'centered_value_diagnostics': 15,
                      'full_generator_diagnostics': 6,
                      'odd_generalized_harmonic_diagnostics': 6,
                      'centered_Faulhaber_exact_checks': 9,
                      'maximum_centered_error': result['numerical_checks']['maximum_absolute_diagnostic_error'],
                      'maximum_truncation_difference': result['numerical_checks']['maximum_two_truncation_difference'],
                      'result_file': str(destination)}, indent=2))


if __name__ == '__main__':
    main()
