#!/usr/bin/env python3
"""Exact finite checks and numerical illustrations for Hahn--Fuchsian systems.

This is a finite rational-exponent implementation, not a proof assistant and
not an algorithm for arbitrary real or infinite supports. All matrix checks
use exact SymPy arithmetic. The crossover checks use mpmath, not intervals.
"""
from __future__ import annotations

import json
import platform
import random
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

import mpmath as mp
import sympy as sp

Exponent = sp.Rational
Series = Dict[Exponent, sp.Matrix]


def is_zero(M: sp.Matrix) -> bool:
    return all(sp.cancel(v) == 0 for v in M)


def clean(M: sp.Matrix) -> sp.Matrix:
    return M.applyfunc(sp.cancel)


def semigroup_to(generators: Iterable[Exponent], cutoff: Exponent) -> List[Exponent]:
    """Enumerate a finitely generated positive rational semigroup up to cutoff."""
    gs = sorted(set(map(sp.Rational, generators)))
    if any(g <= 0 for g in gs):
        raise ValueError("Every generator must be positive.")
    if cutoff < 0:
        raise ValueError("The cutoff must be nonnegative.")
    seen = {sp.Rational(0)}
    todo = [sp.Rational(0)]
    while todo:
        q = todo.pop()
        for g in gs:
            z = q + g
            if z <= cutoff and z not in seen:
                seen.add(z)
                todo.append(z)
    return sorted(seen - {sp.Rational(0)})


def projection(F: sp.Matrix, gamma: Exponent, eigenvalues: Tuple[Exponent, ...]) -> sp.Matrix:
    m = len(eigenvalues)
    return sp.Matrix(m, m, lambda i, j: F[i, j] if eigenvalues[i]-eigenvalues[j] == gamma else 0)


def homological_inverse(F: sp.Matrix, gamma: Exponent,
                        eigenvalues: Tuple[Exponent, ...], N: sp.Matrix) -> sp.Matrix:
    """Inverse of gamma-ad(S+N) on the nonresonant ad(S) blocks."""
    m = len(eigenvalues)

    def diagonal_inverse(M: sp.Matrix) -> sp.Matrix:
        return sp.Matrix(m, m, lambda i, j:
                         0 if gamma == eigenvalues[i]-eigenvalues[j]
                         else M[i, j]/(gamma-eigenvalues[i]+eigenvalues[j]))

    term = diagonal_inverse(F)
    result = sp.zeros(m)
    for _ in range(2*m-1):
        result += term
        term = diagonal_inverse(N*term-term*N)
    assert is_zero(term), "Nilpotent homological inverse did not terminate."
    return clean(result)


def normalize(eigenvalues: Iterable[Exponent], N: sp.Matrix,
              coefficients: Series, cutoff: Exponent) -> Tuple[Series, Series, sp.Matrix, int]:
    lam = tuple(map(sp.Rational, eigenvalues))
    m = len(lam)
    S = sp.diag(*lam)
    if N.shape != (m, m) or not is_zero(S*N-N*S) or not is_zero(N**m):
        raise ValueError("N must be nilpotent and commute with the diagonal S.")
    A = {sp.Rational(g): sp.Matrix(M) for g, M in coefficients.items()}
    if any(g <= 0 or M.shape != (m, m) for g, M in A.items()):
        raise ValueError("Invalid positive coefficient data.")
    support = semigroup_to(A.keys(), sp.Rational(cutoff))
    zero = sp.zeros(m)
    H: Series = {sp.Rational(0): sp.eye(m)}
    R: Series = {}
    for gamma in support:
        F = A.get(gamma, zero).copy()
        for alpha, M in A.items():
            beta = gamma-alpha
            if beta > 0 and beta in H:
                F += M*H[beta]
        for eta, M in R.items():
            beta = gamma-eta
            if beta > 0 and beta in H:
                F -= H[beta]*M
        F = clean(F)
        H[gamma] = homological_inverse(F, gamma, lam, N)
        Rgamma = clean(projection(F, gamma, lam))
        if not is_zero(Rgamma):
            R[gamma] = Rgamma
        assert is_zero(projection(H[gamma], gamma, lam))
    B = N.copy()
    for M in R.values():
        B += M
    B = clean(B)
    assert is_zero(B**m)
    # Check the full gauge equation coefficientwise through the claimed cutoff.
    A0 = S+N
    checks = 0
    for gamma in [sp.Rational(0)] + support:
        Hgamma = H.get(gamma, zero)
        residual = gamma*Hgamma-A0*Hgamma+Hgamma*A0
        for alpha, M in A.items():
            beta = gamma-alpha
            if beta >= 0 and beta in H:
                residual -= M*H[beta]
        for eta, M in R.items():
            beta = gamma-eta
            if beta >= 0 and beta in H:
                residual += H[beta]*M
        assert is_zero(residual), f"Gauge residual failed at exponent {gamma}."
        checks += 1
    return H, R, B, checks


def matrix_json(M: sp.Matrix) -> list:
    return [[str(M[i,j]) for j in range(M.cols)] for i in range(M.rows)]


def crossover_tail(t: mp.mpf, N: int, p: mp.mpf) -> Tuple[mp.mpf, int]:
    """Tail via Hurwitz-zeta expansion; reliable when t/(N+1) stays bounded."""
    if N < 1 or t <= 0 or p <= 1:
        raise ValueError("Require N>=1, t>0, p>1.")
    total = mp.mpf('0')
    factorial_term = mp.mpf('1')
    for k in range(1, 1000):
        factorial_term *= t/k
        add = factorial_term*mp.zeta(p+k-1, N+1)
        total += add
        if k > 12 and abs(add) < mp.mpf('1e-65')*max(1, abs(total)):
            return total, k
    raise ArithmeticError("Hurwitz-zeta series did not reach the tolerance.")


def run() -> dict:
    random.seed(20260929)
    checks = 0
    cases = []
    # Exact symbolic indirect resonance.
    a,b,c,d,e = sp.symbols('a b c d e')
    H,R,B,n = normalize([0,2], sp.zeros(2),
        {sp.Rational(1):sp.Matrix([[a,b],[c,d]]),
         sp.Rational(2):sp.Matrix([[0,0],[e,0]])}, sp.Rational(3))
    checks += n
    expected = sp.Matrix([[0,0],[e+c*(a-d),0]])
    assert is_zero(B-expected)
    cases.append({'name':'symbolic indirect resonance', 'B':matrix_json(B)})
    # Sharp logarithmic chain, for every rank 1,...,7.
    for m in range(1,8):
        J = sp.zeros(m)
        for j in range(m-1):
            J[j+1,j] = 1
        H,R,B,n = normalize(range(m), sp.zeros(m), {sp.Rational(1):J}, sp.Rational(m+1))
        checks += n
        assert B == J
        assert B**m == sp.zeros(m)
        if m > 1:
            assert not is_zero(B**(m-1))
        cases.append({'name':f'sharp chain rank {m}', 'max_log_degree':m-1})
    # Nilpotent blocks and resonances together; all values are exact rationals.
    for k in range(24):
        m = 2 if k % 2 == 0 else 3
        lam = [0,2] if m == 2 else [0,0,1]
        Nmat = sp.zeros(m)
        if m == 3:
            Nmat[0,1] = 1
        A = {sp.Rational(j,2):sp.Matrix(m,m,lambda i,l:sp.Rational(random.randint(-2,2),3))
             for j in (1,2,3)}
        H,R,B,n = normalize(lam,Nmat,A,sp.Rational(4))
        checks += n
        ranks = [int((B**j).rank()) for j in range(m+1)]
        cases.append({'name':f'rational system {k+1}', 'ranks_of_B_powers':ranks})
    # An exact series solution for the induced-log example.
    H,R,B,n = normalize([0,2],sp.zeros(2),
                       {sp.Rational(1):sp.Matrix([[1,0],[1,0]])},sp.Rational(10))
    checks += n
    for j in range(1,11):
        assert H[sp.Rational(j)][0,0] == 1/sp.factorial(j)
        target = -1 if j == 1 else 0 if j == 2 else sp.Rational(1,(j-2)*sp.factorial(j-1))
        assert H[sp.Rational(j)][1,0] == target
    assert B == sp.Matrix([[0,0],[1,0]])
    # ProveIt edit (2026-09-29): record this checked system too; the delivered
    # program checked it but did not list it, so exact_cases had 32 entries
    # while exact_gauge_systems was the literal 33.
    cases.append({'name':'induced-log example a=c=1, b=d=e=0', 'B':matrix_json(B),
                  'series_coefficients_checked_through_exponent':10})
    # Finite versions of the accumulating counterexample have exactly the
    # claimed coefficients. Their convergence/divergence is proved in the paper.
    for j in range(2,21):
        gamma = sp.Rational(2)-sp.Rational(1,j)
        forcing = sp.Rational(1,j*j)
        assert forcing/(gamma-2) == -sp.Rational(1,j)
        checks += 1
    mp.mp.dps = 85
    numerics = []
    for pstr in ['1.5','2','2.5']:
        p = mp.mpf(pstr)
        for cstr in ['0.5','1','2']:
            cval = mp.mpf(cstr)
            f = lambda s: s**(1-p)*mp.expm1(1/s)
            # Smooth series avoids endpoint issues for nonintegral p.
            phi = mp.nsum(lambda k: (1/cval)**(p+k-2)/(mp.factorial(k)*(p+k-2)),[1,mp.inf])
            f1 = mp.diff(f,cval,1)
            f3 = mp.diff(f,cval,3)
            for tint in [20,40,80,160]:
                t = mp.mpf(tint)
                Nint = int(cval*t)
                tail, terms = crossover_tail(t,Nint,p)
                scaled = tail/t**(2-p)
                approx = phi-f(cval)/(2*t)-f1/(12*t*t)
                error = scaled-approx
                # Euler--Maclaurin with its fourth-derivative remainder bound.
                bound = abs(f3)/(360*t**4)
                assert abs(error) <= bound*mp.mpf('1.00000001')
                lo = t*(Nint+1)**(1-p)/(p-1)
                hi = t*mp.exp(t/(Nint+1))*Nint**(1-p)/(p-1)
                assert lo <= tail <= hi
                numerics.append({'p':pstr,'c':cstr,'t':tint,'N':Nint,
                    'scaled_tail':mp.nstr(scaled,24),'Phi':mp.nstr(phi,24),
                    'two_correction_approximation':mp.nstr(approx,24),
                    'error':mp.nstr(error,12),'proved_error_bound':mp.nstr(bound,12),
                    't4_times_error':mp.nstr(t**4*error,16),
                    'predicted_t4_limit':mp.nstr(f3/720,16),'terms':terms})
    return {'status':'all checks passed', 'seed':20260929,
        'environment':{'python':platform.python_version(),'sympy':sp.__version__,'mpmath':mp.__version__},
        'exact_gauge_systems':len(cases),'exact_coefficient_checks_including_counterexample':checks,
        'crossover_cases':len(numerics),'exact_cases':cases,'crossover':numerics,
        'scope':'Finite exact rational/symbolic checks and non-interval numerical illustrations; not a proof of the general theorems.'}


if __name__ == '__main__':
    result = run()
    output = Path(__file__).with_name('results.json')
    # ProveIt edit (2026-09-29): write LF on every platform.
    output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:result[k] for k in ['status','exact_gauge_systems',
          'exact_coefficient_checks_including_counterexample','crossover_cases','environment']},indent=2))
    print(f'Results written to {output}')
