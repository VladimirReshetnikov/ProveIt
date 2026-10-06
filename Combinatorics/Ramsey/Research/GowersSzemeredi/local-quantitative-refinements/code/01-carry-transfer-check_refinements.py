#!/usr/bin/env python3
"""Symbolic identities and deterministic numerical stress tests.

These checks supplement, and do not replace, the proofs in the article.
Requires NumPy and SymPy. Exact carry-pattern certification is separate.
"""
from __future__ import annotations
import json
import math
from pathlib import Path
import numpy as np
import sympy as sp


def phi(delta: float, s: float, q: np.ndarray | float):
    return np.sqrt((q - delta)**2 + 4*delta*(1-delta)*q*(1-q)*s*s)


def sharp_max(delta: float, kappa: float, s: float) -> float:
    return delta*(kappa-s*s)/(kappa*(1-(1-delta)*kappa)-delta*s*s)


def symbolic_checks() -> dict[str, bool]:
    d, q, s, k, t = sp.symbols('d q s k t', real=True)
    b = 1-d
    F = (q-d)**2 + 4*d*b*q*(1-q)*s*s
    curvature_num = sp.expand((2*F*sp.diff(F,q,2)-sp.diff(F,q)**2)/4)
    assert sp.factor(curvature_num-4*d*d*b*b*s*s*(1-s*s)) == 0
    astar = d*(k-s*s)/(k*(1-b*k)-d*s*s)
    squared_equation = (d+q*(2*b*k-1))**2-F
    assert sp.factor(squared_equation.subs(q,astar)) == 0
    tstar = sp.factor(astar-d)
    assert sp.factor(tstar-d*b*(k*k-s*s)/(k*(1-b*k)-d*s*s)) == 0
    half_increment = 3*d*b*k/(4-(4-3*d)*k)
    assert sp.factor(tstar.subs(s,k/2)-half_increment) == 0
    inv = k*(d*b*k-t*(1-b*k))/(d*(b-t))
    assert sp.factor((s*s-inv).subs(t,tstar)) == 0
    # s=0 stop-loss coefficient.
    a = d+t
    phizero = a-d
    u = (phizero-d)/a
    B = d+d*u
    C = 1-2*d-u
    D = sp.symbols('D', real=True)
    assert sp.factor((D-B)/C-(D*(d+t)-2*d*t)/(2*d*(b-t))) == 0
    return {'curvature': True, 'max_density_squared_equation': True,
            'max_density_increment': True, 'half_arc_increment': True,
            'pareto_inverse': True, 'L1_tail_formula': True}


def numerical_checks() -> dict[str, int]:
    # Fixed grids and seed make the run fully reproducible.
    rng = np.random.default_rng(20261006)
    chord_cases = extremal_cases = max_cases = 0
    grid = np.linspace(0, 1, 401)
    for d in [0.01, 0.05, 0.2, 0.5, 0.8, 0.95, 0.99]:
        for s in [0., 0.01, 0.1, 0.3, 0.7, 0.99]:
            for frac in [0., 0.1, 0.5, 0.9, 0.99]:
                a = d+(1-d)*frac
                u = (float(phi(d,s,a))-d)/a
                B = d+d*u
                C = 1-2*d-u
                assert C > 0
                upper = d+u*grid+C*np.maximum(grid-a,0)/(1-a)
                assert np.max(phi(d,s,grid)-upper) < 2e-12
                chord_cases += 1
                M = 2*d*(1-d)
                eta = B+(M-B)*0.37
                lam = (eta-B)/C
                weights = np.array([1-lam-(d-lam)/a, (d-lam)/a, lam])
                qs = np.array([0., a, 1.])
                assert weights.min() > -1e-10
                assert abs(np.dot(weights,qs)-d) < 1e-11
                assert abs(np.dot(weights,phi(d,s,qs))-eta) < 1e-11
                assert abs(np.dot(weights,np.maximum(qs-a,0))/(1-a)-lam) < 1e-11
                extremal_cases += 1
        for kap in [0.01, 0.1, 0.4, 0.9, 1.]:
            for frac in [0., 0.1, 0.5, 0.9, 0.999]:
                s = kap*frac
                a = sharp_max(d,kap,s)
                assert d-1e-10 <= a <= 1+1e-10
                B = d+d*(float(phi(d,s,a))-d)/a
                assert abs(B-2*d*(1-d)*kap) < 1e-10
                max_cases += 1
    # Test the sharp cell envelope for independently sampled weighted atoms.
    cell_cases = 2000
    for _ in range(cell_cases):
        d, s = rng.uniform(.01,.99), rng.uniform(0,.999)
        theta = math.asin(s)
        w = rng.random(12); w /= w.sum()
        h = rng.random(12)
        angles = rng.uniform(-theta,theta,12)
        q = float(np.dot(w,h))
        z = np.dot(w*(h-d),np.exp(1j*angles))
        assert abs(z) <= phi(d,s,q)+1e-12
    return {'chord_cases': chord_cases, 'extremal_cases': extremal_cases,
            'max_density_cases': max_cases, 'weighted_cell_cases': cell_cases}


def progression_tests() -> list[dict[str, float | int]]:
    reports = []
    for N in (120, 1000, 4096):
        for density in (.1,.3,.5):
            h = np.zeros(N); h[:int(density*N)] = 1
            d = h.mean()
            for freq in (1, 2, 7):
                psi = np.exp(2j*np.pi*freq*np.arange(N)/N)
                eta = abs(np.dot(h-d,psi)/N)
                if eta < 1e-10:
                    continue
                kap = min(1.,eta/(2*d*(1-d)))
                theta = math.asin(kap/2); r = theta/math.pi
                L = max(1,math.floor(math.sqrt(N*r/2)))
                if L == 1:
                    qstep = 1
                    cells = [[i] for i in range(N)]
                else:
                    Q = math.ceil(2*(L-1)/r)
                    # Exact modular test for rational frequency freq/N.
                    qstep = next(q for q in range(1,Q+1)
                                 if min((freq*q)%N, N-(freq*q)%N)*Q < N)
                    cells = []
                    for start in range(qstep):
                        row = list(range(start,N,qstep))
                        nblocks, rem = divmod(len(row),L)
                        assert nblocks >= 1
                        offset = 0
                        for j in range(nblocks):
                            size = L+(rem if j == nblocks-1 else 0)
                            cells.append(row[offset:offset+size]); offset += size
                        assert offset == len(row)
                flattened = [x for c in cells for x in c]
                assert sorted(flattened) == list(range(N))
                assert min(map(len,cells)) >= L and max(map(len,cells)) <= 2*L-1
                err = min((freq*qstep)%N,N-(freq*qstep)%N)/N
                if L >= 2:
                    assert (max(map(len,cells))-1)*err <= r+1e-12
                predicted = sharp_max(d,kap,kap/2)
                actual = max(float(h[c].mean()) for c in cells)
                assert actual+1e-10 >= predicted
                reports.append({'N': N, 'density': d, 'frequency': freq,
                                'eta': eta, 'L': L, 'step': qstep,
                                'predicted_density': predicted, 'actual_density': actual})
    return reports


def tables() -> dict:
    counts = []
    for k in [2,3,4,8,12,16]:
        H = (k-2)*2**(k-1)+1
        R = sum(math.comb(H,j) for j in range(min(k,H)+1))
        J = k*2**(k-1)
        B = (2*(k+1))**k * sum(math.comb(J,j) for j in range(min(k+1,J)+1))
        counts.append({'k': k, 'r': 1, 'H': H, 'old_bits': 2*k**3,
                       'new_upper_bits': k+math.log2(R),
                       'orbit_upper_bits_r_k_plus_1': math.log2(B)})
    increments = []
    N = 10**12
    for d,eta in [(.5,.1),(.1,.02),(.01,.002),(.01,.01)]:
        kap = eta/(2*d*(1-d))
        L = max(1,math.floor(math.sqrt(N*math.asin(kap/2)/(2*math.pi))))
        increments.append({'N':N,'delta':d,'eta':eta,'old_length':math.sqrt(eta**3*N/(128*math.pi)),
                           'new_length':L,'old_increment':eta/8,
                           'new_increment':sharp_max(d,kap,kap/2)-d})
    return {'entropy':counts,'increments':increments}


def main() -> None:
    result = {'symbolic':symbolic_checks(), 'numerical':numerical_checks(),
              'progressions':progression_tests(), 'tables':tables(),
              'status':'All checks passed. Numerical tests are not formal proofs.'}
    out = Path(__file__).resolve().parents[1]/'results'/'refinement_checks.json'
    out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k not in ('progressions','tables')},indent=2))
    print(f'Progression cases: {len(result["progressions"])}; result file: {out}')


if __name__ == '__main__':
    main()
