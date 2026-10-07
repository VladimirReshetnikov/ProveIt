#!/usr/bin/env python3
"""Independent finite checks for the characteristic-five quotient theorem.

Exact symbolic coefficient identities are distinguished from floating-point
checks on finite groups. Neither substitutes for the universal proof.
"""
from itertools import product
from pathlib import Path
import json
import numpy as np
import sympy as sp


class FourierGroup:
    def __init__(self, p=5, dimension=2):
        self.p = p
        self.points = np.array(list(product(range(p), repeat=dimension)), dtype=int)
        self.n = len(self.points)
        index = {tuple(x): i for i, x in enumerate(self.points)}
        self.add = np.array([[index[tuple((x+y) % p)] for y in self.points]
                             for x in self.points])
        self.neg = np.array([index[tuple(-x % p)] for x in self.points])
        self.sub = self.add[:, self.neg]
        self.double = self.add[np.arange(self.n), np.arange(self.n)]
        self.line = np.all(self.points[:, 1:] == 0, axis=1)

    def squares(self, a):
        ans = np.empty((self.n, self.n), complex)
        for s in range(self.n):
            # Rows are t, columns are r.
            ans[s] = np.sum(a[None, :] * np.conj(a[self.add[s]])[None, :]
                            * np.conj(a[self.add])
                            * a[self.add[s, self.add]], axis=1)
        return ans

    def stats(self, a):
        lam = abs(a)**2
        T = self.squares(a)
        norm8 = float(np.sum(abs(T)**2))
        S = float(np.sum(lam**2))
        B = float(np.sum(a[self.double] * np.conj(a)**3 * a).real)
        H = float(np.sum(lam[:, None]*lam[None, :]*lam[self.neg[self.add]]))
        J = np.sum(lam[:, None]*a[None, :]**2*a[self.sub]
                   *np.conj(a[self.add]))
        K = np.sum(a[:, None]**2*a[None, :]**2*a[self.neg[self.add]]**2)
        L = (2*np.real(a[:, None]*a[None, :]*np.conj(a[self.add]))
             +2*np.real(a[:, None]*np.conj(a[None, :])*np.conj(a[self.sub])))
        C6 = float((12*H+12*J+4*K).real)
        C7 = float(2*np.vdot(T, L).real)
        return dict(norm8=norm8, S=S, B=B, H=H, C6=C6, C7=C7, T=T, L=L)


def symbolic_series():
    k, s = sp.symbols('k s', real=True)
    q = sp.Pow(2, sp.Rational(-3, 4))
    R = q-k**2*s/2-sp.Rational(9, 8)*k**4*s**2/q+sp.Rational(3, 4)*k**6*s**3/q**2
    norm = 8*R**4+16*R**3*k**2*s+48*R**2*k**4*s**2+16*R*k**6*s**3+8*k**8*s**4
    assert sp.simplify(sp.series(norm-1, s, 0, 4).removeO()) == 0
    objective = (24*(R**2-q**2)/s + 16*R**2*k
                 + s*(24*k**4+96*R**2*k**2+1)
                 + s**2*(48*R*k**4+32*R**2*k**3))
    series = sp.series(objective, s, 0, 3).removeO().expand()
    H0, H2, H4 = [sp.simplify(series.coeff(s, i)) for i in range(3)]
    k0 = q/3
    assert sp.simplify(sp.diff(H0, k).subs(k, k0)) == 0
    shift = sp.simplify(-sp.diff(H2, k).subs(k, k0)/sp.diff(H0, k, 2))
    correction = sp.simplify(H4.subs(k, k0)
                - sp.diff(H2, k).subs(k, k0)**2/(2*sp.diff(H0, k, 2)))
    assert sp.simplify(H0.subs(k, k0)-2**sp.Rational(3, 4)/3) == 0
    assert sp.simplify(H2.subs(k, k0)-sp.Rational(20, 9)) == 0
    assert sp.simplify(correction-sp.Rational(869, 216)*q) == 0
    assert sp.simplify(shift-sp.Rational(31, 27)*q**2) == 0
    return {'type': 'exact symbolic identities', 'q': str(q),
            'H0': str(H0), 'H2': str(H2), 'H4': str(H4),
            'amplitude_shift': str(shift), 'u10_coefficient': str(correction),
            'u10_decimal': str(sp.N(correction, 30))}


def rational_cutoff_certificate():
    from fractions import Fraction as F
    a, b, cutoff = F(193, 250), F(2, 25), F(1, 100000)
    upper_R = 8*(a**3*b+a**2*b**2+a*b**3)
    assert 8*a**8 > 1
    assert b**4 > 4*cutoff
    assert F(7, 10)-12*cutoff > F(2, 3)
    assert upper_R < F(1, 3)
    assert -2+40*cutoff+280*cutoff**2+92*cutoff**3 < -1
    return {'type': 'exact rational cutoff certificate',
            't_maximum': str(cutoff), 'R_rational_upper_bound': str(upper_R),
            'all_inequalities_passed': True}


def finite_checks():
    rng = np.random.default_rng(20261006)
    G = FourierGroup()
    maximum_identity_error = 0.0
    minimum_gap_ratio = float('inf')
    local_cases = 0
    for trial in range(160):
        raw = rng.normal(size=G.n)+1j*rng.normal(size=G.n)
        a = (raw+np.conj(raw[G.neg]))/2
        a[0] = 0
        if trial < 100:
            a *= 10**rng.uniform(-5, -1.7)
            i1 = np.flatnonzero(np.all(G.points == (1, 0), axis=1))[0]
            i2 = G.double[i1]
            phase = rng.uniform(0, 2*np.pi)
            a[i1] = np.exp(1j*phase)
            a[G.neg[i1]] = np.conj(a[i1])
            a[i2] = 10**rng.uniform(-5, -1.7)*np.exp(2j*phase)
            a[G.neg[i2]] = np.conj(a[i2])
        a /= G.stats(a)['norm8']**(1/8)
        F = G.stats(a)
        weight = a.copy()
        weight[0] = 0.37
        direct = np.sum(abs(G.squares(weight))**2)
        poly = (0.37**8+12*0.37**4*F['S']+8*0.37**3*F['B']
                +0.37**2*F['C6']+0.37*F['C7']+F['norm8'])
        err = abs(direct-poly)
        maximum_identity_error = max(maximum_identity_error, float(err))
        assert err < 2e-11
        g = np.where(G.line, a, 0)
        P = G.stats(g)
        D = float(np.sum(abs(a[~G.line])**4))
        Delta = F['norm8']-P['norm8']
        offaxes = G.line[:, None] & G.line[None, :]
        offaxes[0, :] = False
        offaxes[:, 0] = False
        R = float(np.sum(abs(P['T'][offaxes])))
        assert Delta+2e-12 >= (10*P['S']-2*R)*D+2*D**2
        if P['S'] >= 2/3 and R <= 1/3 and Delta > 1e-12:
            local_cases += 1
            assert Delta+2e-12 >= 6*D
            assert F['H']-P['H'] <= 6*Delta+2e-12
            assert abs(F['C6']-P['C6']) <= 168*Delta+2e-12
            assert abs(F['C7']-P['C7']) <= 60*Delta+2e-12
            star = G.stats(g/P['norm8']**(1/8))
            t = 1e-5
            gain = (12*(star['S']-F['S'])+8*t*(star['B']-F['B'])
                    +t*t*(star['C6']-F['C6'])
                    +t**3*(star['C7']-F['C7']))
            assert gain+1e-11 >= Delta
            minimum_gap_ratio = min(minimum_gap_ratio, gain/Delta)
    return {'type': 'floating-point finite checks, not a universal proof',
            'group': 'F_5^2', 'trials': 160, 'local_projection_cases': local_cases,
            'largest_polynomial_identity_error': maximum_identity_error,
            'minimum_gain_over_t4_Delta': minimum_gap_ratio}


if __name__ == '__main__':
    result = {'symbolic_series': symbolic_series(),
              'rational_cutoff_certificate': rational_cutoff_certificate(),
              'finite_checks': finite_checks()}
    path = Path(__file__).resolve().parents[1]/'data'/'quotient_checks.json'
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))
