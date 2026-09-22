#!/usr/bin/env python3
"""Exact finite checks for Infinite Surcomplex Spectral Synthesis.

Python 3.10+ and SymPy. No numerical eigenvalue approximations are used.
This tests finite jets and examples, not the infinite-dimensional theorem.
Run from any directory; writes ../data/verification.json.
"""
from __future__ import annotations
import itertools
import json
from pathlib import Path
import platform
import sympy as s

CHECKS: list[dict[str, object]] = []

def record(name: str, condition: bool) -> None:
    ok = bool(condition)
    CHECKS.append({'name': name, 'passed': ok})
    if not ok:
        raise AssertionError(name)

def clean(A: s.MatrixBase) -> s.Matrix:
    return s.Matrix(A).applyfunc(s.expand)

def diag(A: s.MatrixBase) -> s.Matrix:
    return s.diag(*A.diagonal())

def indices(rank: int, order: int) -> list[tuple[int, ...]]:
    return sorted((a for a in itertools.product(range(order+1), repeat=rank)
                   if sum(a) <= order), key=lambda a: (sum(a), a))

def leq(a: tuple[int, ...], b: tuple[int, ...]) -> bool:
    return all(x <= y for x,y in zip(a,b))

def sub(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(x-y for x,y in zip(a,b))

def mul(P: dict, Q: dict, idx: list, n: int) -> dict:
    out = {}
    for a in idx:
        M = s.zeros(n)
        for b,Pb in P.items():
            if leq(b,a):
                c = sub(a,b)
                if c in Q:
                    M += Pb*Q[c]
        out[a] = clean(M)
    return out

def adj(P: dict) -> dict:
    return {a: clean(M.conjugate().T) for a,M in P.items()}

def diagonalize(d: list, B: dict, order: int, rank: int=1) -> dict:
    """Finite Taylor jets with diag(V)=I and AU=UL, U*U=I."""
    n = len(d)
    idx = indices(rank, order)
    zero = (0,)*rank
    eye = s.eye(n)
    V = {zero: eye}
    L = {zero: s.diag(*d)}
    for a in idx[1:]:
        R = s.zeros(n)
        for b,Bb in B.items():
            if sum(b) and leq(b,a):
                R += Bb*V[sub(a,b)]
        for b,Lb in L.items():
            if sum(b) and leq(b,a):
                c = sub(a,b)
                if sum(c):
                    R -= V[c]*Lb
        R = clean(R)
        L[a] = diag(R)
        V[a] = clean(s.Matrix(n,n,lambda i,j:
                          -R[i,j]/(d[i]-d[j]) if i != j else 0))
    N = mul(adj(V), V, idx, n)
    Q = {a: (M-eye if a == zero else M) for a,M in N.items()}
    power = {zero: eye}
    H = {a: (eye if a == zero else s.zeros(n)) for a in idx}
    for k in range(1, order+1):
        power = mul(power,Q,idx,n)
        for a in idx:
            H[a] += s.binomial(s.Rational(-1,2),k)*power[a]
    H = {a: clean(M) for a,M in H.items()}
    U = mul(V,H,idx,n)
    return {'V':V,'L':L,'U':U,'N':N,'indices':idx}

def certify(name: str, d: list, B: dict, order: int, rank: int=1) -> dict:
    out = diagonalize(d,B,order,rank)
    n = len(d)
    zero = (0,)*rank
    A = {zero:s.diag(*d),**B}
    idx = out['indices']
    U,L,V = out['U'],out['L'],out['V']
    AU,UL = mul(A,U,idx,n),mul(U,L,idx,n)
    UU,UtU = mul(U,adj(U),idx,n),mul(adj(U),U,idx,n)
    for a in idx:
        identity = s.eye(n) if a == zero else s.zeros(n)
        record(f'{name}: eigenidentity {a}', clean(AU[a]-UL[a]) == s.zeros(n))
        record(f'{name}: U*U {a}', UtU[a] == identity)
        record(f'{name}: UU* {a}', UU[a] == identity)
        record(f'{name}: real eigenvalues {a}', clean(L[a]-L[a].conjugate()) == s.zeros(n))
        record(f'{name}: orthogonal V columns {a}', out['N'][a] == diag(out['N'][a]))
    return out

def chain(length: int) -> s.Matrix:
    return s.Matrix(length,length,lambda i,j: 1 if abs(i-j)==1 else 0)

def main() -> None:
    I=s.I
    d = [s.Rational(0),s.Rational(2),s.Rational(5)]
    B1=s.Matrix([[1,1+I,0],[1-I,-2,2*I],[0,-2*I,3]])
    B2=s.Matrix([[0,I,2],[-I,1,1],[2,1,-1]])
    certify('complex Hermitian, two orders',d,{(1,):B1,(2,):B2},6)

    # Distinct labels accumulating at zero; finite chain jets represent
    # the infinite chain wherever the locality theorem licenses them.
    size=6
    levels=[s.Rational(1,k+1) for k in range(size)]
    c = certify('accumulating-level chain',levels,{(1,):chain(size)},10)
    lam=[s.simplify(c['L'][(k,)][0,0]) for k in range(11)]
    record('chain: known second coefficient',lam[2] == 2)
    record('chain: known fourth coefficient',lam[4] == -2)
    for k in range(1,11,2):
        record(f'chain: odd coefficient {k} vanishes',lam[k] == 0)

    # Independently derived closed-form eigenpair for the infinite chain.
    q=s.symbols('q')
    n0=s.symbols('n', integer=True, nonnegative=True)
    tq=q/(1-q**2)
    lq=(1+q**2)/(1-q**2)
    record('closed eigenpair: recurrence',
           s.factor(tq*(n0+(n0+2)*q**2)+q-lq*(n0+1)*q) == 0)
    record('closed eigenpair: quadratic identity',
           s.factor(lq**2-1-4*tq**2) == 0)
    tt=s.symbols('t')
    rootjet=s.sqrt(1+4*tt**2).series(tt,0,12).removeO().expand()
    record('closed eigenpair: all checked energy coefficients',
           all(rootjet.coeff(tt,k)==lam[k] for k in range(11)))
    zz=s.symbols('z')
    normgf=s.diff(zz*s.diff(zz/(1-zz),zz),zz)
    record('closed eigenpair: normalization generating function',
           s.factor(normgf-(1+zz)/(1-zz)**3) == 0)

    # Exact sharpness of the radius-r / order-(2r+2) boundary bound.
    sharp=[]
    for L in range(1,5):
        full_d=[s.Rational(1,k+1) for k in range(L+1)]
        full=diagonalize(full_d,{(1,):chain(L+1)},2*L)
        cut=diagonalize(full_d[:-1],{(1,):chain(L)},2*L)
        differences=[s.simplify(full['L'][(k,)][0,0]-cut['L'][(k,)][0,0])
                     for k in range(2*L+1)]
        expected=1/(full_d[0]-full_d[L])
        for k in range(1,L):
            expected /= (full_d[0]-full_d[k])**2
        record(f'boundary L={L}: lower coefficients equal',all(x==0 for x in differences[:-1]))
        record(f'boundary L={L}: sharp coefficient',differences[-1] == expected)
        sharp.append({'distance':L,'degree':2*L,'coefficient':str(expected)})

    # Two independent positive scales. Their order can be lexicographic;
    # the code checks finite bidegrees, never a cofinality claim.
    B=s.Matrix([[0,1,0],[1,0,0],[0,0,0]])
    C=s.Matrix([[0,0,0],[0,0,1],[0,1,0]])
    m = certify('two independent Hahn scales',[s.Integer(0),s.Integer(1),s.Integer(3)],
                {(1,0):B,(0,1):C},4,rank=2)
    record('two scales: leading distant eigenvector entry',m['U'][(1,1)][2,0] == s.Rational(1,3))
    record('two scales: first return through distant edge',m['L'][(2,2)][0,0] == s.Rational(-1,3))
    record('two scales: initial energy shift',m['L'][(2,0)][0,0] == -1)

    # Rank-one projection identities through the computed order.
    idx=m['indices']; U=m['U']; n=3
    E=s.diag(1,0,0)
    P=mul(mul(U,{(0,0):E},idx,n),adj(U),idx,n)
    PP=mul(P,P,idx,n)
    for a in idx:
        record(f'projection idempotence {a}',PP[a] == P[a])
        record(f'projection self-adjointness {a}',adj(P)[a] == P[a])

    # Exact algebra behind the bounded-operator obstruction.
    nvar=s.symbols('n',integer=True,positive=True)
    invgap=s.simplify(1/(1/nvar-1/(nvar+1)))
    record('unbounded first commutator inverse',invgap == nvar*(nvar+1))

    report={'title':'Exact finite verification for Infinite Surcomplex Spectral Synthesis',
            'python':platform.python_version(),'sympy':s.__version__,
            'checks':len(CHECKS),'passed':sum(bool(c['passed']) for c in CHECKS),
            'accumulating_chain_lambda0_coefficients_0_to_10':list(map(str,lam)),
            'sharp_boundary_examples':sharp,
            'scope':'Finite symbolic checks only. Not a formal proof of arbitrary supports or infinite operators.',
            'details':CHECKS}
    target=Path(__file__).resolve().parent.parent/'data'/'verification.json'
    target.parent.mkdir(exist_ok=True)
    target.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k != 'details'},indent=2))

if __name__=='__main__':
    main()
