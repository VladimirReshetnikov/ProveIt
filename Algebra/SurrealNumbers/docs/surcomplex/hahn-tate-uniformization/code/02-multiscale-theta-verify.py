#!/usr/bin/env python3
"""Exact finite checks for article.tex. Python 3.10+, standard library only.

These check examples, allocation, and finite minimization certificates.
They do not prove Hahn summability, ordinal order types, or the general theorem.
Run from the package root: python3 code/verify.py
"""
from __future__ import annotations
from collections import Counter, deque
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json

Vec = tuple[int, int]

def add(x: Vec, y: Vec) -> Vec:
    return x[0] + y[0], x[1] + y[1]

def sign_sqrt2(a: int, b: int) -> int:
    """Exact sign of a+b*sqrt(2), without floating point."""
    if b == 0:
        return (a > 0) - (a < 0)
    if a == 0:
        return (b > 0) - (b < 0)
    if a > 0 and b > 0:
        return 1
    if a < 0 and b < 0:
        return -1
    c = (a*a > 2*b*b) - (a*a < 2*b*b)
    return c if a > 0 else -c

def shear_nonnegative(x: Vec, y: Vec) -> bool:
    # B=(2*x1*y1, 2*(x2-sqrt(2)*x1)*(y2-sqrt(2)*y1)).
    lead = x[0]*y[0]
    if lead:
        return lead > 0
    return sign_sqrt2(x[1]*y[1] + 2*x[0]*y[0],
                      -(x[0]*y[1]+x[1]*y[0])) >= 0

def allocate(m: int, bins: int, cap: int) -> tuple[list[int], int]:
    if m < 0 or bins <= 0 or cap <= 0:
        raise ValueError('m>=0, bins>0, cap>0 required')
    if m >= bins*cap:
        return [cap]*bins, m-bins*cap
    out = []
    for _ in range(bins):
        take = min(m, cap)
        out.append(take)
        m -= take
    return out, 0

def decompose_shear(x: Vec) -> Counter[Vec]:
    m, n = x
    if not m:
        return Counter({(0, 1 if n > 0 else -1): abs(n)}) if n else Counter()
    eps = 1 if m > 0 else -1
    eta = 1 if n >= 0 else -1
    shifts, residue = allocate(abs(n), abs(m), 2)
    out = Counter((eps, eta*k) for k in shifts)
    if residue:
        out[(0, eta)] += residue
    return out

def energy(x: Vec, beta: tuple[F, F, F]) -> tuple[F, F]:
    """Q-energy (m², n²+mn-m²), with b=(c*m,a*m+b*n)."""
    m, n = x
    c, a, b = beta
    return F(m*m)+c*m, F(n*n+m*n-m*m)+a*m+b*n

S = sorted({(a,b) for a in (-1,1) for b in (-1,0,1)} | {(0,-1),(0,1)})

def descend(start: Vec, beta: tuple[F,F,F]) -> tuple[Vec,int]:
    x = start
    steps = 0
    # Limit is only a defensive check for this finite test run.
    while True:
        e = energy(x,beta)
        nxt = next((add(x,s) for s in S if energy(add(x,s),beta)<e),None)
        if nxt is None:
            return x,steps
        x = nxt
        steps += 1
        if steps > 10000:
            raise AssertionError('finite example exceeded defensive step limit')

def minima_graph(start: Vec,beta: tuple[F,F,F]) -> set[Vec]:
    value = energy(start,beta)
    seen = {start}
    queue = deque([start])
    while queue:
        x = queue.popleft()
        for s in S:
            y = add(x,s)
            if energy(y,beta) == value and y not in seen:
                seen.add(y)
                queue.append(y)
    return seen

def floor_fraction(a: F) -> int:
    return a.numerator//a.denominator

def analytic_minima(beta: tuple[F,F,F]) -> set[Vec]:
    """Independent exact quotientwise minimization, not a box cutoff."""
    c,a,b=beta
    k=floor_fraction(-c/2)
    ms=[k,k+1]
    first=min(F(m*m)+c*m for m in ms)
    candidates=[]
    for m in ms:
        if F(m*m)+c*m != first:
            continue
        ell=floor_fraction(-(F(m)+b)/2)
        candidates.extend([(m,ell),(m,ell+1)])
    least=min(energy(x,beta) for x in candidates)
    return {x for x in candidates if energy(x,beta)==least}

# Truncated ordinary series over Q, used only for an exact theta row.
def mul(a: list[F],b: list[F],N: int)->list[F]:
    return [sum((a[i]*b[k-i] for i in range(k+1)),F(0)) for k in range(N+1)]

def inv(a:list[F],N:int)->list[F]:
    if not a[0]:
        raise ValueError('nonzero constant coefficient required')
    out=[1/a[0]]+[F(0)]*N
    for k in range(1,N+1):
        out[k]=-sum((a[i]*out[k-i] for i in range(1,k+1)),F(0))/a[0]
    return out

def power(a:list[F],n:int,N:int)->list[F]:
    if n<0:
        return power(inv(a,N),-n,N)
    out=[F(1)]+[F(0)]*N
    base=a[:]
    while n:
        if n&1:
            out=mul(out,base,N)
        base=mul(base,base,N)
        n//=2
    return out

def row_residual(y:list[F],N:int)->list[F]:
    # Outer-coordinate-zero row: sum_n u^{n(n-1)} y^n + sum_n u^{n²} y^n.
    out=[F(0)]*(N+1)
    # |n|>N+2 cannot contribute to exponent <=N for either quadratic.
    for n in range(-N-2,N+3):
        for exponent in (n*(n-1),n*n):
            if exponent<=N:
                yp=power(y,n,N)
                for j in range(N-exponent+1):
                    out[exponent+j]+=yp[j]
    return out

def root_row(N:int)->list[F]:
    y=[F(-2)]+[F(0)]*N
    assert row_residual(y,N)[0]==0
    for k in range(1,N+1):
        # The coefficient of the new y_k is 1 because reduction is 2+y.
        y[k]=-row_residual(y,N)[k]
    assert row_residual(y,N)==[F(0)]*(N+1)
    return y

def main()->None:
    count=0
    for x in product(range(-20,21),repeat=2):
        dec=decompose_shear(x)
        assert tuple(sum(a[i]*k for a,k in dec.items()) for i in (0,1)) == x
        assert all(k>0 for k in dec.values())
        assert all(shear_nonnegative(a,b) for a in dec for b in dec)
        count+=1
    allocations=0
    for bins in range(1,12):
        for cap in range(1,6):
            for m in range(101):
                cs,r=allocate(m,bins,cap)
                assert sum(cs)+r==m and all(0<=c<=cap for c in cs)
                assert not r or all(c==cap for c in cs)
                allocations+=1
    cases=0
    max_steps=0
    max_minima=0
    for c,a,b in product(range(-4,5),range(-3,4),range(-3,4)):
        beta=F(c),F(a),F(b)
        first,steps=descend((9,-11),beta)
        got=minima_graph(first,beta)
        expect=analytic_minima(beta)
        assert got==expect
        assert len(got)<=4
        # Verify graph distances, using the proven S rather than all differences.
        for start in got:
            distances={start:0}
            queue=deque([start])
            while queue:
                x=queue.popleft()
                for s in S:
                    y=add(x,s)
                    if y in got and y not in distances:
                        distances[y]=distances[x]+1
                        queue.append(y)
            assert len(distances)==len(got) and max(distances.values())<=2
        cases+=1
        max_steps=max(max_steps,steps)
        max_minima=max(max_minima,len(got))
    pell=[]
    p,q=1,0
    for k in range(1,13):
        p,q=p+2*q,p+q
        assert p*p-2*q*q==(-1)**k
        pell.append({'k':k,'p':p,'q':q,'norm':p*p+q*q})
    beta=F(-1),F(1),F(-1)
    first,steps=descend((8,-9),beta)
    special=sorted(minima_graph(first,beta))
    assert special==[(0,0),(0,1),(1,0)]
    root=root_row(8)
    result={
        'arithmetic':'Exact integers and fractions; sqrt(2) signs are exact.',
        'scope':'Finite example checks only, not machine proofs of the theorems.',
        'allocation_cases':allocations,
        'irrational_shear_decompositions':count,
        'rational_energy_parameter_cases':cases,
        'max_descent_steps_in_test':max_steps,
        'max_minimizers_in_test':max_minima,
        'special_minimizers':special,
        'special_descent_steps':steps,
        'root_row_coefficients_degree_0_to_8':[str(a) for a in root],
        'pell_witnesses':pell,
        'status':'ALL CHECKS PASSED'
    }
    rootpath=Path(__file__).resolve().parent.parent
    (rootpath/'data').mkdir(exist_ok=True)
    (rootpath/'data'/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
