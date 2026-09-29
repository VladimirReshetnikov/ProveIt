#!/usr/bin/env python3
"""Exact checks for Eventual Optimality in Binary DFAO Reversal.

Standard library only. All finite tests supplement, not replace, the proofs.
Run from any working directory. Do not interpret a tested range as a tail bound.
"""
from __future__ import annotations
import csv
import json
import math
import platform
from collections import deque
from functools import cache
from itertools import product
from pathlib import Path
import random

OUT = Path(__file__).resolve().parents[1] / 'results'
COUNTS: dict[str, int] = {}

def check(condition: bool, label: str) -> None:
    if not condition:
        raise AssertionError(label)
    COUNTS[label.split(':')[0]] = COUNTS.get(label.split(':')[0], 0) + 1

@cache
def stirling(n: int, j: int) -> int:
    if n == 0:
        return int(j == 0)
    if j < 1 or j > n:
        return 0
    return j * stirling(n - 1, j) + stirling(n - 1, j - 1)

@cache
def chromatic(k: int, a: int, b: int) -> int:
    """Number of k-colorings of K_{a,b}; a,b positive."""
    if min(a, b) < 1 or k < 1:
        raise ValueError('positive graph sides and palette required')
    return sum(math.factorial(k) // math.factorial(k-i)
               * stirling(a, i) * (k-i)**b
               for i in range(1, min(a, k-1)+1))

def chromatic_ie(k: int, a: int, b: int) -> int:
    """Independent inclusion-exclusion formula (no Stirling calls)."""
    return sum(math.comb(k,i) * (k-i)**b *
               sum((-1)**(i-j) * math.comb(i,j) * j**a
                   for j in range(i+1))
               for i in range(1,k))

def split(n: int) -> tuple[int, int]:
    d = 1 if n % 2 else (2 if n % 4 == 0 else 4)
    return (n-d)//2, (n+d)//2

def returned(k: int, a: int, b: int) -> int:
    return max(a,b) if k == 3 else a*b

def candidate_defect(n: int, k: int) -> int:
    a,b = split(n)
    return chromatic(k,a,b) - returned(k,a,b)

@cache
def product_order_bound(r: int) -> int:
    """Largest product of positive parts with sum r, empty product = 1."""
    if r <= 1:
        return 1
    q,s = divmod(r,3)
    if s == 0:
        return 3**q
    if s == 1:
        return 4*3**(q-1)
    return 2*3**q

def universal_defect_bound(n: int, k: int) -> tuple[int, str]:
    """Enumerate all collision-orbital graph types, never automata.

    This is a lower bound on the missing-coloring count of EVERY pair.
    Residual order is bounded by the maximal product of cycle lengths.
    """
    records = [(k**(n-1), 'two_permutations'),
               ((k-1)**2*k**(n-2)-1, 'two_singular'),
               (k**n-(k-1)**n, 'nonsurjective')]
    for m in range(2,n+1):
        r=n-m
        order=m*product_order_bound(r)
        for d in range(1,m):
            if m % d:
                continue
            ell=m//d
            c=(k-1)**ell+(-1)**ell*(k-1)
            records.append((c**d*k**r-order, f'cycle:{m}:{d}:{r}'))
    for a in range(1,n//2+1):
        for b in range(a,n-a+1):
            r=n-a-b
            d=math.gcd(a,b)
            p=chromatic(k,a//d,b//d)**d*k**r
            support_order=b if k == 3 and d == 1 else math.lcm(a,b)
            order=support_order*product_order_bound(r)
            records.append((p-order,f'bipartite:{a}:{b}:{d}:{r}'))
    return min(records)

def primitive_word(length: int, colors: list[int]) -> tuple[int,...]:
    if not 1 <= len(colors) <= length:
        raise ValueError('palette does not fit')
    if len(colors) == 1:
        return (colors[0],)*length
    return tuple(colors) + (colors[-1],)*(length-len(colors))

def witness(n: int, k: int) -> tuple[tuple[int,...], ...]:
    if not 7 <= n or not 3 <= k < n:
        raise ValueError('witness requires n >= 7 and 3 <= k < n')
    a,b=split(n)
    p=tuple(list(range(1,a))+[0]+list(range(a+1,n))+[a])
    s=list(range(n))
    s[0]=a
    s[-1]=0
    if a % 2:
        s[1],s[2]=s[2],s[1]
    left_count=1 if k == 3 else min(a,k-2)
    tau=primitive_word(a,list(range(left_count))) + primitive_word(b,list(range(left_count,k)))
    return p,tuple(s),tau

def orbit(generators: tuple[tuple[int,...],...], tau: tuple[int,...], cap: int=1_000_000) -> set[tuple[int,...]]:
    seen={tau}
    pending=deque([tau])
    while pending:
        c=pending.popleft()
        for g in generators:
            nxt=tuple(c[x] for x in g)
            if nxt not in seen:
                seen.add(nxt)
                pending.append(nxt)
                if len(seen)>cap:
                    raise RuntimeError('orbit exceeded explicit resource limit')
    return seen

def orbital_edges(p: tuple[int,...], x: int, y: int) -> set[tuple[int,int]]:
    edges=set()
    pair=tuple(sorted((x,y)))
    while pair not in edges:
        edges.add(pair)
        pair=tuple(sorted((p[pair[0]],p[pair[1]])))
    return edges

def cycle_of(p: tuple[int,...], x: int) -> list[int]:
    out=[x]
    while p[out[-1]] != x:
        out.append(p[out[-1]])
    return out

def graph_prediction(k: int, p: tuple[int,...], x: int, y: int) -> int:
    cx=cycle_of(p,x)
    if y in cx:
        m=len(cx); d=math.gcd(m,cx.index(y)); ell=m//d
        return ((k-1)**ell+(-1)**ell*(k-1))**d*k**(len(p)-m)
    cy=cycle_of(p,y); a=len(cx);b=len(cy);d=math.gcd(a,b)
    return chromatic(k,a//d,b//d)**d*k**(len(p)-a-b)

def polynomial_multiply(p: list[int], q: list[int]) -> list[int]:
    out=[0]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):
            out[i+j]+=a*b
    return out

def main() -> None:
    OUT.mkdir(exist_ok=True)
    for n in range(1,36):
        for j in range(1,n+1):
            check(stirling(n,j)**2 >= stirling(n,j-1)*stirling(n,j+1),'stirling_logconcavity')
    for a in range(1,18):
        for b in range(a,23):
            for i in range(1,a+1):
                for j in range(i+1,b+1):
                    check(stirling(a,i)*stirling(b,j)>=stirling(a,j)*stirling(b,i),'stirling_TP2')
    for k in range(3,13):
        for a in range(1,20):
            for b in range(1,20):
                check(chromatic(k,a,b)==chromatic_ie(k,a,b),'chromatic_IE')
                check(chromatic(k,a,b)==chromatic(k,b,a),'chromatic_symmetry')
        for n in range(4,81):
            for a in range(1,(n-2)//2+1):
                b=n-a
                diff=chromatic(k,a,b)-chromatic(k,a+1,b-1)
                lower=k*(k-1)*(k-2)*(2**(b-2)-2**(a-1))
                check(diff>=lower>0,'quantitative_balancing')
    finite=[]
    for n in range(7,101):
        a,b=split(n)
        check(math.gcd(a,b)==1 and 1<a<b,'nearest_coprime_split')
        for k in range(3,min(n,13)):
            cand=candidate_defect(n,k)
            lower,typ=universal_defect_bound(n,k)
            check(lower<=cand,'universal_bound_consistency')
            finite.append({'n':n,'k':k,'a':a,'b':b,'candidate_defect':cand,
                           'universal_lower_bound':lower,'certifies_equality':int(lower==cand),
                           'minimizing_type':typ})
    with (OUT/'finite_certificates.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(finite[0]));w.writeheader();w.writerows(finite)
    bfs=[]
    for n,k in [(7,3),(8,3),(9,3),(10,3),(7,4),(8,4),(7,5),(8,5)]:
        p,s,tau=witness(n,k)
        found=orbit((p,s),tau)
        expected=k**n-candidate_defect(n,k)
        check(len(found)==expected,'witness_BFS')
        a,b=split(n)
        improper=sum(1 for c in found if set(c[:a])&set(c[a:]))
        check(improper==k**n-chromatic(k,a,b),'improper_saturation_BFS')
        check(len(found)-improper==returned(k,a,b),'proper_period_BFS')
        bfs.append({'n':n,'k':k,'p':p,'s':s,'tau':tau,'orbit_size':len(found),
                    'improper_states':improper,'proper_states':len(found)-improper})
    (OUT/'bfs_witnesses.json').write_text(json.dumps(bfs,indent=2)+'\n')
    rng=random.Random(20260928)
    for _ in range(120):
        n=rng.randrange(2,8);k=rng.randrange(3,5)
        p=list(range(n));rng.shuffle(p);p=tuple(p)
        x,y=rng.sample(range(n),2)
        edges=orbital_edges(p,x,y)
        actual=sum(all(c[u]!=c[v] for u,v in edges) for c in product(range(k),repeat=n))
        check(actual==graph_prediction(k,p,x,y),'orbital_graph_direct_count')
    for _ in range(120):
        n=rng.randrange(3,7);k=rng.randrange(3,min(n,4)+1)
        a=tuple(rng.randrange(n) for _ in range(n))
        b=tuple(rng.randrange(n) for _ in range(n))
        tau=tuple(rng.randrange(k) for _ in range(n))
        actual=k**n-len(orbit((a,b),tau))
        lower,_=universal_defect_bound(n,k)
        check(actual>=lower,'random_automaton_bound')
    recurrence=[]
    for k in range(3,11):
        bases=sorted({u*v for u in range(1,k) for v in range(1,k-u+1)})
        poly=[1]
        for _ in range(2 if k==3 else 3):
            poly=polynomial_multiply(poly,[-1,1])
        for b in bases:
            if b!=1:
                poly=polynomial_multiply(poly,[-b*b,1])
        for r in range(4):
            for t in range(k+2,k+15):
                vals=[candidate_defect(4*(t+j)+r,k) for j in range(len(poly))]
                check(sum(c*v for c,v in zip(poly,vals))==0,'residue_recurrence')
        recurrence.append({'k':k,'product_bases':bases,'annihilator_ascending':poly})
    (OUT/'recurrences.json').write_text(json.dumps(recurrence,indent=2)+'\n')
    ratios=[]
    for k in range(3,11):
        m=k//2;s=math.sqrt(m*(k-m));lam=math.log((m+1)/m) if k%2 else 0
        for n in [80,81,82,83,160,161,162,163]:
            a,b=split(n)
            constant=(2*math.comb(k,m)*math.cosh(lam*(b-a)/2) if k%2 else math.comb(k,m))
            ratio=candidate_defect(n,k)/(s**n)
            ratios.append({'n':n,'k':k,'scaled_defect':ratio,'asymptotic_constant':constant,'ratio':ratio/constant})
    with (OUT/'asymptotic_ratios.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(ratios[0]));w.writeheader();w.writerows(ratios)
    summary={'python':platform.python_version(),'checks':COUNTS,'total_checks':sum(COUNTS.values()),
             'finite_rows':len(finite),'finite_equalities':sum(r['certifies_equality'] for r in finite),
             'finite_failures_to_certify':[[r['n'],r['k']] for r in finite if not r['certifies_equality']],
             'bfs_states_visited':sum(r['orbit_size'] for r in bfs),
             'scope':'Finite structural bounds are exact-integer computations, not Lean proofs or a uniform tail theorem.'}
    (OUT/'verification_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':
    main()
