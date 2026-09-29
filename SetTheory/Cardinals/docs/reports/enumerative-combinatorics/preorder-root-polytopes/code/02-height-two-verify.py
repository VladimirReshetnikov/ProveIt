#!/usr/bin/env python3
"""Exact certificates for height-two preorder support polynomials.

Python 3.10+, standard library only. Run from any directory:
    python3 code/verify.py
The mathematical proofs, rather than these finite checks, establish the
infinite-family statements. All arithmetic used for assertions is exact.
"""
from __future__ import annotations
import csv
import json
from functools import lru_cache
from itertools import combinations
from math import comb
from pathlib import Path
from random import Random
from time import perf_counter

ROOT = Path(__file__).resolve().parents[1]
INTERVALS = [(1,1),(1,2),(1,3),(1,4),(1,5),(2,6),(3,8),(4,9)]
EXPECTED_GAMMA = [1,32,336,1420,2534,1946,658,86,3]
EXPECTED_H = [1,49,952,9828,61302,248816,688516,1337738,1857081,
              1857081,1337738,688516,248816,61302,9828,952,49,1]

def check(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)

def trim(a: list[int]) -> list[int]:
    while len(a)>1 and a[-1]==0: a.pop()
    return a

def add(*polys: list[int]) -> list[int]:
    out = [0]*max(map(len,polys), default=1)
    for a in polys:
        for i,c in enumerate(a): out[i] += c
    return trim(out)

def scale(a: list[int], c: int) -> list[int]:
    return trim([c*x for x in a])

def derivative(a: list[int]) -> list[int]:
    return [i*a[i] for i in range(1,len(a))] or [0]

def evaluate(a: list[int], x: int) -> int:
    out=0
    for c in reversed(a): out=out*x+c
    return out

def gamma_to_h(g: list[int], n: int) -> list[int]:
    out=[0]*(n+1)
    for k,c in enumerate(g):
        if c==0: continue
        check(2*k<=n, 'Gamma degree exceeds half the ground-set size')
        for j in range(n-2*k+1): out[k+j]+=c*comb(n-2*k,j)
    return out

def matching_supports(p: int, neighbors: list[int]) -> set[tuple[int,int]]:
    """Deduplicate pairs of covered shores, NOT individual matchings."""
    check(p>=0 and all(0<=N<(1<<p) for N in neighbors),'Invalid graph')
    states={(0,0)}
    for j,N in enumerate(neighbors):
        new=set(states)
        for X,Y in states:
            choices=N&~X
            while choices:
                bit=choices&-choices; choices-=bit
                new.add((X|bit,Y|(1<<j)))
        states=new
    return states

def pm_polynomial(p: int, neighbors: list[int]) -> list[int]:
    out=[0]*(min(p,len(neighbors))+1)
    for X,_ in matching_supports(p,neighbors): out[X.bit_count()]+=1
    return trim(out)

def ordered_board(p: int, intervals: list[tuple[int,int]]) -> list[list[list[int]]]:
    """Increasing-chain recurrence, independent of the subset-state algorithm."""
    q=len(intervals)
    check(all(1<=l<=r<=p for l,r in intervals),'Invalid interval')
    check(all(intervals[j][0]<=intervals[j+1][0] and
              intervals[j][1]<=intervals[j+1][1] for j in range(q-1)),
          'Intervals must have nondecreasing endpoints')
    F=[[[1] for _ in range(q+1)] for _ in range(p+1)]
    for i in range(1,p+1):
        for j in range(1,q+1):
            diagonal=F[i-1][j-1]
            edge_term=[0]+diagonal if intervals[j-1][0]<=i<=intervals[j-1][1] else [0]
            F[i][j]=add(F[i-1][j],F[i][j-1],scale(diagonal,-1),edge_term)
    return F

def weak_vectors(k: int, total: int):
    if k==0:
        yield ()
        return
    for v in range(total+1):
        for rest in weak_vectors(k-1,total-v): yield (v,)+rest

def neighborhood_unions(neighbors: list[int]) -> list[int]:
    U=[0]*(1<<len(neighbors))
    for S in range(1,len(U)):
        bit=S&-S; U[S]=U[S^bit]|neighbors[bit.bit_length()-1]
    return U

def direct_h(p: int, neighbors: list[int]) -> list[int]:
    """Enumerate integer points from ideal inequalities; no gamma identity."""
    q=len(neighbors); U=neighborhood_unions(neighbors)
    h=[0]*(p+q+1)
    for Z in range(1<<p):
        bounds=[S.bit_count()+(U[S]&Z).bit_count() for S in range(1<<q)]
        for b in weak_vectors(q,q+Z.bit_count()):
            sums=[0]*(1<<q); good=True
            for S in range(1,1<<q):
                bit=S&-S; sums[S]=sums[S^bit]+b[bit.bit_length()-1]
                if sums[S]>bounds[S]: good=False; break
            if good: h[p-Z.bit_count()+sum(v>0 for v in b)]+=1
    return h

def polymatroid_count(p: int, neighbors: list[int]) -> int:
    U=neighborhood_unions(neighbors); count=0
    for c in weak_vectors(len(neighbors),p):
        sums=[0]*len(U); good=True
        for S in range(1,len(U)):
            bit=S&-S; sums[S]=sums[S^bit]+c[bit.bit_length()-1]
            if sums[S]>U[S].bit_count(): good=False; break
        count+=good
    return count

# Exact arithmetic in Z[zeta], zeta^2-zeta+1=0.
Eis=tuple[int,int]
ZERO: Eis=(0,0)
ONE: Eis=(1,0)
ZETA: Eis=(0,1)
def eadd(x: Eis,y: Eis) -> Eis: return (x[0]+y[0],x[1]+y[1])
def eneg(x: Eis) -> Eis: return (-x[0],-x[1])
def emul(x: Eis,y: Eis) -> Eis:
    a,b=x; c,d=y
    return (a*c-b*d,a*d+b*c+b*d)
def enorm(x: Eis) -> int:
    a,b=x; return a*a+a*b+b*b

def determinant(M: tuple[tuple[Eis,...],...]) -> Eis:
    """Laplace expansion memoized by remaining-column mask."""
    n=len(M)
    @lru_cache(None)
    def go(mask: int) -> Eis:
        if mask==0: return ONE
        row=n-mask.bit_count(); ans=ZERO; pos=0; remaining=mask
        while remaining:
            bit=remaining&-remaining; remaining-=bit
            value=emul(M[row][bit.bit_length()-1],go(mask^bit))
            ans=eadd(ans,eneg(value) if pos%2 else value); pos+=1
        return ans
    return go((1<<n)-1)

def cactus_minor_test(p: int,q: int,edges: list[tuple[int,int]],
                      marked: dict[tuple[int,int],int]) -> dict:
    """marked edge gets sign*zeta; all other existing edges get 1."""
    ns=[0]*q
    for a,b in edges: ns[b]|=1<<a
    supports=matching_supports(p,ns)
    B=[[ZERO]*q for _ in range(p)]
    for a,b in edges:
        sign=marked.get((a,b),0)
        B[a][b]=ZETA if sign==1 else eneg(ZETA) if sign==-1 else ONE
    checked=0
    for k in range(min(p,q)+1):
        for X in combinations(range(p),k):
            for Y in combinations(range(q),k):
                sub=tuple(tuple(B[a][b] for b in Y) for a in X)
                value=enorm(determinant(sub))
                pair=(sum(1<<a for a in X),sum(1<<b for b in Y))
                check(value==int(pair in supports),'Cactus minor has incorrect norm')
                checked+=1
    return {'p':p,'q':q,'edges':edges,'marked':[[*e,s] for e,s in marked.items()],
            'minors_checked':checked,'gamma':pm_polynomial(p,ns)}

def crown_graph(r: int) -> list[int]:
    return [(1<<j)|(1<<((j+1)%r)) for j in range(r)]

def run() -> dict:
    t0=perf_counter()
    ns=[sum(1<<(i-1) for i in range(l,r+1)) for l,r in INTERVALS]
    g=pm_polynomial(9,ns); F=ordered_board(9,INTERVALS)
    check(g==EXPECTED_GAMMA,'Counterexample support enumeration mismatch')
    check(F[9][8]==g,'Counterexample board recurrence mismatch')
    h=gamma_to_h(g,17); check(h==EXPECTED_H,'Counterexample expansion mismatch')
    vals=[evaluate(g,-2),evaluate(derivative(g),-2),evaluate(derivative(derivative(g)),-2)]
    defect=vals[1]**2-vals[0]*vals[2]
    check(vals==[65,-560,4912] and defect==-5680,'Laguerre certificate mismatch')
    count=0
    for bits in range(1<<9):
        nbs=[(bits>>(3*j))&7 for j in range(3)]
        p=pm_polynomial(3,nbs)
        check(direct_h(3,nbs)==gamma_to_h(p,6),'Small-graph h mismatch')
        check(polymatroid_count(3,nbs)==sum(p),'Polymatroid count mismatch')
        count+=1
    rng=Random(20260928)
    for _ in range(24):
        nbs=[rng.randrange(16) for _ in range(3)]
        check(direct_h(4,nbs)==gamma_to_h(pm_polynomial(4,nbs),7),
              'Random 4+3 direct check failed')
    crowns=[]
    for r in range(2,9):
        nbs=crown_graph(r); cg=pm_polynomial(r,nbs)
        formula=[(2*r*comb(2*r-k,k))//(2*r-k) for k in range(r+1)]
        formula[-1]-=1
        check(cg==formula,'Crown formula mismatch')
        if r<=4: check(direct_h(r,nbs)==gamma_to_h(cg,2*r),'Crown direct h mismatch')
        crowns.append({'r':r,'gamma':cg,'h':gamma_to_h(cg,2*r)})
    cases=[]
    for r in range(2,6):
        edges=[(j,j) for j in range(r)]+[((j+1)%r,j) for j in range(r)]
        cases.append(cactus_minor_test(r,r,edges,{(0,0):(-1)**r}))
    # A square and a hexagon sharing a single vertex a_0 (4+5 vertices).
    edges=[(0,0),(1,0),(1,1),(0,1),
           (0,2),(2,2),(2,3),(3,3),(3,4),(0,4)]
    cases.append(cactus_minor_test(4,5,edges,{(0,0):1,(0,2):-1}))
    # The same cactus with a bridge to one new vertex in each shore.
    edges2=edges+[(1,5),(4,5)]
    cases.append(cactus_minor_test(5,6,edges2,{(0,0):1,(0,2):-1}))
    results={'counterexample':{'intervals':INTERVALS,'neighbors_masks':ns,
              'gamma':g,'h':h,'matching_supports':sum(g),'lattice_points':sum(h),
              'evaluation_at_minus_two':vals,'laguerre_defect':defect,
              'board_last_row':[F[9][j] for j in range(9)]},
             'small_tests':{'all_labeled_3_by_3_graphs':count,'random_4_by_3_graphs':24,
                            'seed':20260928},
             'crowns':crowns,'cactus_minors':cases,
             'seconds':round(perf_counter()-t0,3),'all_tests_passed':True}
    out=ROOT/'data'; out.mkdir(exist_ok=True)
    (out/'verification.json').write_text(json.dumps(results,indent=2)+'\n')
    with (out/'board_certificate.csv').open('w',newline='') as fp:
        writer=csv.writer(fp); writer.writerow(['i','j','coefficients_in_ascending_degree'])
        for i in range(10):
            for j in range(9): writer.writerow([i,j,json.dumps(F[i][j])])
    print(json.dumps(results,indent=2))
    return results

if __name__=='__main__': run()
