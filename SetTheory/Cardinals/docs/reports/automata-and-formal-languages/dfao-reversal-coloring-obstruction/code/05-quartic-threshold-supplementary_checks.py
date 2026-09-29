#!/usr/bin/env python3
"""Small independent enumerations and identity tests. Standard library only."""
from __future__ import annotations
import csv
import json
from collections import Counter, deque
from itertools import combinations, permutations, product
from math import comb, factorial, gcd
from pathlib import Path
from theorem_checks import chromatic, nearest_split

ROOT = Path(__file__).resolve().parents[1]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


def positive_chromatic(a: int, b: int, k: int) -> int:
    s = [1] + [0] * k
    for _ in range(a):
        s = [0] + [j * s[j] + s[j-1] for j in range(1, k+1)]
    return sum(factorial(k)//factorial(k-j) * s[j] * (k-j)**b
               for j in range(k+1))


def orbit(tau: tuple[int, ...], generators: tuple[tuple[int, ...], ...]) -> set:
    found = {tau}
    queue = deque([tau])
    while queue:
        c = queue.popleft()
        for t in generators:
            target = tuple(c[tq] for tq in t)
            if target not in found:
                found.add(target)
                queue.append(target)
    return found


def main() -> None:
    report = {}
    counts = 0
    for k in range(3, 10):
        for a in range(13):
            for b in range(13):
                require(chromatic(a,b,k) == positive_chromatic(a,b,k), "Palette identity")
                counts += 1
    report['signed_positive_identity_tests'] = counts
    counts = 0
    for n in range(2, 2001):
        a = next(i for i in range(n//2, 0, -1) if gcd(i,n-i)==1)
        require(nearest_split(n)==(a,n-a), "Nearest split")
        counts += 1
    report['nearest_split_tests'] = counts
    counts = 0
    for k in range(3, 11):
        for n in range(4, 61):
            for a in range(2,n//2+1):
                require(chromatic(a-1,n-a+1,k)>chromatic(a,n-a,k), "Strict balancing")
                counts += 1
    report['strict_balance_tests'] = counts
    # Exhaustive graph-orbit classification through five vertices, k=3.
    counts = 0
    colorings = {n:list(product(range(3),repeat=n)) for n in range(2,6)}
    for n in range(2,6):
        for p in permutations(range(n)):
            cycles = []
            seen = set()
            for root in range(n):
                if root in seen:
                    continue
                c=[]; x=root
                while x not in seen:
                    seen.add(x);c.append(x);x=p[x]
                cycles.append(c)
            for x,y in combinations(range(n),2):
                edges=set();u,v=x,y
                while tuple(sorted((u,v))) not in edges:
                    edges.add(tuple(sorted((u,v))));u,v=p[u],p[v]
                ci = next(c for c in cycles if x in c)
                cj = next(c for c in cycles if y in c)
                if ci is cj:
                    m=len(ci); step=(ci.index(y)-ci.index(x))%m
                    d=gcd(m,step);ell=m//d
                    expected=(2**ell+(-1)**ell*2)**d*3**(n-m)
                else:
                    a,b=len(ci),len(cj);d=gcd(a,b)
                    expected=positive_chromatic(a//d,b//d,3)**d*3**(n-a-b)
                actual=sum(all(c[u]!=c[v] for u,v in edges) for c in colorings[n])
                require(actual==expected,"Collision graph classification")
                counts += 1
    report['exhaustive_graph_classification_tests'] = counts
    # Count nu=0 and nu=1 by literal color assignments.
    rank_records=[]
    for k in (3,4,5):
        for a in range(1,4):
            for b in range(1,4):
                spectrum=Counter()
                exactly_one_edge=0
                for c in product(range(k),repeat=a+b):
                    left=Counter(c[:a]);right=Counter(c[a:])
                    nu=sum(min(left[g],right[g]) for g in range(k))
                    spectrum[nu]+=1
                    if sum(left[g]*right[g] for g in range(k))==1:
                        exactly_one_edge+=1
                m1=k*sum(comb(a,i)*comb(b,j)*positive_chromatic(a-i,b-j,k-1)
                         for i in range(1,a+1) for j in range(1,b+1) if min(i,j)==1)
                require(spectrum[0]==chromatic(a,b,k),"nu=0")
                require(spectrum[1]==m1,"nu=1")
                require(exactly_one_edge==k*a*b*positive_chromatic(a-1,b-1,k-1),"One edge")
                rank_records.append(dict(k=k,a=a,b=b,spectrum=dict(spectrum),one_edge=exactly_one_edge))
    report['rank_matching_enumerations']=len(rank_records)
    # Structurally necessary conditions are not sufficient for saturation.
    p=(1,2,0,4,5,6,3)
    s=(0,1,2,0,4,5,6)
    tau=(0,0,1,2,2,2,3)
    reached=orbit(tau,(p,s))
    pure=orbit(tau,(p,))
    require(len(pure)==12,"Pure period")
    require(len(set(s))==6,"Rank")
    require(all(tuple(c[:3]) in {(0,0,1),(0,1,0),(1,0,0)} for c in reached),"Invariant block")
    report['nonsaturating_example']=dict(n=7,k=4,p=p,s=s,tau=tau,
                                       orbit_size=len(reached),pure_period=len(pure),
                                       optimum=4**7-chromatic(3,4,4)+12)
    # Sample exact optimum values, all inside the fully closed slices.
    rows=[]
    for n in range(7,13):
        a,b=nearest_split(n)
        row={'n':n,'a':a,'b':b}
        for k in range(4,8):
            row[f'k{k}']=k**n-chromatic(a,b,k)+a*b if k<n else ''
        rows.append(row)
    out=ROOT/'results';out.mkdir(exist_ok=True)
    (out/'supplementary.json').write_text(json.dumps(report,indent=2)+'\n')
    (out/'rank_matching_enumerations.json').write_text(json.dumps(rank_records,indent=2)+'\n')
    with (out/'sample_values.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
