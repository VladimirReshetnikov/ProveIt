#!/usr/bin/env python3
"""Exact finite checks for Surreal Markov Generators at Every Valuation Scale.

Requires Python 3.10+ and SymPy.  No floating point arithmetic or external data.
These checks validate examples and finite instances, not the general theorems.
Run from the archive root: python code/verify.py
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
import random
import sympy as sp

Gamma = tuple[F, ...]

def add(x: Gamma, y: Gamma) -> Gamma:
    assert len(x) == len(y)
    return tuple(a+b for a,b in zip(x,y))
def sub(x: Gamma, y: Gamma) -> Gamma:
    return tuple(a-b for a,b in zip(x,y))
def mul(x: Gamma, n: int | F) -> Gamma:
    return tuple(a*n for a in x)

def rat(x: F) -> sp.Rational:
    return sp.Rational(x.numerator, x.denominator)

@dataclass(frozen=True)
class Edge:
    gamma: Gamma
    coefficient: F
    def __post_init__(self) -> None:
        if self.coefficient <= 0:
            raise ValueError('Every existing edge must have positive leading coefficient.')

@dataclass(frozen=True)
class Forest:
    arcs: int
    gamma: Gamma
    coefficient: F
    roots: tuple[int, ...]

def forests(n: int, edges: dict[tuple[int,int], Edge]) -> list[Forest]:
    if n < 2 or not edges:
        raise ValueError('Use at least two vertices and a nonempty edge set.')
    rank = len(next(iter(edges.values())).gamma)
    zero = (F(0),)*rank
    choices = [[None]+[j for j in range(n) if (i,j) in edges] for i in range(n)]
    ans: list[Forest] = []
    for parents in product(*choices):
        roots = []
        for i in range(n):
            seen: set[int] = set()
            j = i
            while parents[j] is not None:
                if j in seen:
                    break
                seen.add(j)
                j = parents[j]
            else:
                roots.append(j)
                continue
            break
        if len(roots) != n:
            continue
        gamma, coefficient, arcs = zero, F(1), 0
        for i,j in enumerate(parents):
            if j is not None:
                e = edges[i,j]
                gamma = add(gamma,e.gamma)
                coefficient *= e.coefficient
                arcs += 1
        ans.append(Forest(arcs,gamma,coefficient,tuple(roots)))
    return ans

def profile(n: int, fs: list[Forest]):
    a, b, B = [], [], []
    for k in range(n):
        group = [f for f in fs if f.arcs == k]
        if not group:
            raise ValueError('This checker expects a strongly connected graph.')
        ak = min(f.gamma for f in group)
        best = [f for f in group if f.gamma == ak]
        bk = sum((f.coefficient for f in best),F(0))
        M = sp.zeros(n)
        for f in best:
            for i,j in enumerate(f.roots):
                M[i,j] += rat(f.coefficient)
        a.append(ak); b.append(rat(bk)); B.append(M)
    return a,b,B

def active(a: list[Gamma], alpha: Gamma) -> list[int]:
    d = len(a)-1
    values = [add(ak,mul(alpha,d-k)) for k,ak in enumerate(a)]
    m = min(values)
    return [k for k,v in enumerate(values) if v == m]

def critical(a: list[Gamma]) -> list[Gamma]:
    candidates = {mul(sub(a[l],a[k]),F(1,l-k))
                  for k in range(len(a)) for l in range(k+1,len(a))}
    return sorted(x for x in candidates if len(active(a,x)) > 1)

def kernel(a,b,B,alpha,c=sp.Integer(1)):
    d = len(a)-1
    inds = active(a,alpha)
    den = sum(b[k]*c**(d-k) for k in inds)
    num = sp.zeros(len(a))
    for k in inds:
        num += B[k]*c**(d-k)
    return num/den

def stochastic_split(P: sp.Matrix):
    n = P.rows
    reachable = [[bool(i == j or P[i,j] > 0) for j in range(n)] for i in range(n)]
    for k in range(n):
        for i in range(n):
            for j in range(n):
                reachable[i][j] |= reachable[i][k] and reachable[k][j]
    unused = set(range(n)); classes = []
    while unused:
        i = min(unused)
        cls = {j for j in unused if reachable[i][j] and reachable[j][i]}
        unused -= cls
        if all(P[j,k] == 0 for j in cls for k in range(n) if k not in cls):
            classes.append(sorted(cls))
    U = sp.Matrix(n,len(classes),lambda i,a: sum(P[i,j] for j in classes[a]))
    V = sp.Matrix([list(P[cls[0],:]) for cls in classes])
    assert U*V == P and V*U == sp.eye(len(classes))
    assert all(x >= 0 for x in U) and all(x >= 0 for x in V)
    assert U*sp.ones(U.cols,1) == sp.ones(n,1)
    assert V*sp.ones(n,1) == sp.ones(V.rows,1)
    return U,V

def check_instance(n: int, edges: dict[tuple[int,int], Edge]) -> dict:
    fs = forests(n,edges)
    a,b,B = profile(n,fs)
    levels = critical(a)
    increments = [sub(a[k],a[k-1]) for k in range(1,n)]
    assert increments == sorted(increments)
    assert sorted(set(increments)) == levels
    unit = (F(0),)*(len(a[0])-1)+(F(1),)
    samples = [sub(levels[0],unit)]
    samples += [mul(add(x,y),F(1,2)) for x,y in zip(levels,levels[1:])]
    samples += [add(levels[-1],unit)]
    projectors = [kernel(a,b,B,x) for x in samples]
    assert projectors[0] == sp.eye(n)
    assert projectors[-1].rank() == 1
    for j,P in enumerate(projectors):
        assert P*P == P
        assert P*sp.ones(n,1) == sp.ones(n,1)
        assert all(x >= 0 for x in P)
        assert P.rank() == n-active(a,samples[j])[0]
        for Q in projectors[j:]:
            assert P*Q == Q and Q*P == Q
    for j,alpha in enumerate(levels):
        P,Q = projectors[j:j+2]
        U,V = stochastic_split(P)
        Ks = [kernel(a,b,B,alpha,sp.Integer(c)) for c in (1,2,3)]
        H = V*Ks[0]*U
        assert H.det() != 0
        G = H.inv()-sp.eye(H.rows)
        assert G*sp.ones(G.rows,1) == sp.zeros(G.rows,1)
        assert all(G[i,k] <= 0 for i in range(G.rows) for k in range(G.cols) if i != k)
        assert G.rank() == P.rank()-Q.rank()
        for c,K in zip((1,2,3),Ks):
            assert K == U*(c*(c*sp.eye(G.rows)+G).inv())*V
            assert P*K == K and K*Q == Q
        assert Ks[0]*Ks[1] == 2*Ks[0]-Ks[1]
    return {'n':n,'forest_count':len(fs),'critical_scale_count':len(levels)}

def direct_checks():
    s,t,c = sp.symbols('s t c', positive=True)
    L = sp.Matrix([[2,-2,0],[-1,1+3*t,-3*t],[-t,0,t]])
    D = sp.expand((s*sp.eye(3)+L).det()/s)
    assert sp.expand(D-(s**2+(3+4*t)*s+9*t+3*t**2)) == 0
    P = sp.Matrix([[F(1,3),F(2,3),0],[F(1,3),F(2,3),0],[0,0,1]])
    Q = sp.ones(3,1)*sp.Matrix([[F(1,9),F(2,9),F(2,3)]])
    R = s*(s*sp.eye(3)+L).inv()
    slow = R.subs(s,c*t).applyfunc(lambda x: sp.limit(x,t,0))
    assert (slow-(c*P+3*Q)/(c+3)).applyfunc(sp.simplify) == sp.zeros(3)
    # Universal flag construction, including an idempotent with transient mass.
    P1 = sp.Matrix([[1,0,0],[0,1,0],[F(1,3),F(2,3),0]])
    P2 = sp.ones(3,1)*sp.Matrix([[F(1,4),F(3,4),0]])
    assert P1*P2 == P2 and P2*P1 == P2
    H = t*(sp.eye(3)-P1)+t**4*(P1-P2)
    expected = P2+s/(s+t)*(sp.eye(3)-P1)+s/(s+t**4)*(P1-P2)
    assert (s*(s*sp.eye(3)+H).inv()-expected).applyfunc(sp.factor) == sp.zeros(3)
    eps=t**7
    J=sp.ones(3)/3
    Lplus=H+eps*(sp.eye(3)-J)
    Rplus=s*(s*sp.eye(3)+Lplus).inv()
    formula=(s*sp.eye(3)+eps*J)*((s+eps)*sp.eye(3)+H).inv()
    assert (Rplus-formula).applyfunc(sp.factor) == sp.zeros(3)
    # A valuation bound sharp at every positive integral perturbation order.
    eta = sp.symbols('eta', positive=True)
    relative = sp.factor(((1+eta)/(3+eta))/(sp.Rational(1,3))-1)
    assert relative == 2*eta/(eta+3)
    # Symbolic forest identity for a four-state directed graph.
    edges={(0,1):Edge((F(0),),F(2)),(1,2):Edge((F(1),),F(3)),
           (2,3):Edge((F(2),),F(1)),(3,0):Edge((F(1),),F(2)),
           (1,0):Edge((F(0),),F(1)),(3,2):Edge((F(2),),F(4))}
    fs=forests(4,edges)
    lap=sp.zeros(4); den=0; num=sp.zeros(4)
    for (i,j),e in edges.items():
        q=rat(e.coefficient)*t**int(e.gamma[0]); lap[i,i]+=q; lap[i,j]-=q
    for f in fs:
        w=rat(f.coefficient)*t**int(f.gamma[0])*s**(3-f.arcs)
        den+=w
        for i,j in enumerate(f.roots): num[i,j]+=w
    assert sp.expand((s*sp.eye(4)+lap).det()-s*den) == 0
    assert ((s*sp.eye(4)+lap)*num-s*den*sp.eye(4)).applyfunc(sp.expand) == sp.zeros(4)
    # General prescribed-crossover construction.  The intermediate filler
    # repairs a forbidden positive off-diagonal without adding a leading scale.
    Afast=sp.Matrix([[1,-1,0,0],[0,1,-1,0],[-1,0,1,0],[0,0,0,0]])
    Vfast=sp.Matrix([[sp.Rational(1,3)]*3+[0],[0,0,0,1]])
    Ufast=sp.Matrix([[1,0],[1,0],[1,0],[0,1]])
    Pfast=Ufast*Vfast
    Gslow=sp.Matrix([[2,-2],[-1,1]])
    Alift=Ufast*Gslow*Vfast
    Hcascade=Afast+t*(sp.eye(4)-Pfast)+t**2*Alift
    assert (Afast+t**2*Alift)[0,2] == 2*t**2/3
    assert Hcascade[0,2] == 2*t**2/3-t/3
    expectedR=(s*((s+t)*sp.eye(4)+Afast).inv()*(sp.eye(4)-Pfast)
               +Ufast*(s*(s*sp.eye(2)+t**2*Gslow).inv())*Vfast)
    assert ((s*sp.eye(4)+Hcascade)*expectedR-s*sp.eye(4)).applyfunc(sp.factor)==sp.zeros(4)
    expectedD=(s+3*t**2)*((s+t)**2+3*(s+t)+3)
    assert sp.expand((s*sp.eye(4)+Hcascade).det()-s*expectedD)==0
    middle=expectedR.subs(s,c*t).applyfunc(lambda x:sp.limit(x,t,0))
    assert middle==Pfast
    atslow=expectedR.subs(s,c*t**2).applyfunc(lambda x:sp.limit(x,t,0))
    assert (atslow-Ufast*(c*(c*sp.eye(2)+Gslow).inv())*Vfast).applyfunc(sp.factor)==sp.zeros(4)
    return {'three_state_characteristic':str(D),
            'prescribed_crossover_realization':'exact block identity and shadows passed',
            'positivity_filler_no_new_scale':'exact t-scale shadow equals old plateau',
            'universal_flag_resolvent':'exact symbolic identity passed',
            'irreducible_completion':'exact symbolic identity passed',
            'four_state_matrix_forest':'exact symbolic identity passed',
            'sharp_relative_error':str(relative)}

def main() -> None:
    seed=20260922
    rng=random.Random(seed)
    records=[]
    for trial in range(48):
        n=2+trial%4
        edges={}
        for i in range(n):
            for j in range(n):
                if i != j:
                    gamma=(F(rng.randrange(-1,4)),F(rng.randrange(-2,4)))
                    edges[i,j]=Edge(gamma,F(rng.randrange(1,6),rng.randrange(1,4)))
        records.append(check_instance(n,edges))
    symbolic=direct_checks()
    report={'status':'PASS','seed':seed,'arithmetic':'exact rational; lexicographic Q^2',
            'random_instances':len(records),'enumerated_forests':sum(r['forest_count'] for r in records),
            'critical_kernels_checked':sum(r['critical_scale_count'] for r in records),
            'symbolic_checks':symbolic,'instances':records,
            'scope':'Finite tests only. No Lean verification or proof of the arbitrary-rank theorems.'}
    destination=Path(__file__).resolve().parents[1]/'data'/'verification.json'
    destination.parent.mkdir(exist_ok=True)
    destination.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='instances'},indent=2))

if __name__ == '__main__':
    main()
