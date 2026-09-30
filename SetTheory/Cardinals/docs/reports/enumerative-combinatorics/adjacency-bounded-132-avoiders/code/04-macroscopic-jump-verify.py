#!/usr/bin/env python3
"""Exact finite regression checks for the macroscopic-jump paper.

These tests check finite identities, not the limiting theorems.
Python 3.10+; standard library only. Never run with python -O.
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import permutations
from math import comb
from pathlib import Path
import csv
import json


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def catalan(n: int) -> int:
    if n < 0:
        raise ValueError('n must be nonnegative')
    return comb(2*n, n)//(n+1)


@lru_cache(None)
def avoiders(n: int) -> tuple[tuple[int, ...], ...]:
    if n == 0:
        return ((),)
    return tuple(tuple(x+b for x in left)+(n,)+right
                 for a in range(n) for b in [n-a-1]
                 for left in avoiders(a) for right in avoiders(b))


def avoids_132(p: tuple[int, ...]) -> bool:
    return not any(p[i] < p[k] < p[j]
                   for i in range(len(p)) for j in range(i+1,len(p))
                   for k in range(j+1,len(p)))


def stats(p: tuple[int, ...]) -> tuple[int, int, int, int]:
    if not p:
        return (0,0,0,0)
    return (len(p),p[0],p[-1],max((abs(x-y) for x,y in zip(p,p[1:])),default=0))


def merge(left: tuple[int,int,int,int],right: tuple[int,int,int,int]) -> tuple[int,int,int,int]:
    a,fl,ll,ml=left
    b,fr,lr,mr=right
    n=a+b+1
    f=b+fl if a else n
    if b:
        return n,f,lr,max(n-fr,mr)
    return n,f,n,max(ml,n-ll) if a else 0


def cycle_tree(word: tuple[int, ...]) -> tuple[int, ...]:
    """Rotate +/-1 degree word to its unique valid binary-tree preorder."""
    total=0
    low=0
    start=0
    for i,x in enumerate(word):
        total+=x
        if total<low:
            low=total
            start=i+1
    start%=len(word)
    return word[start:]+word[:start]


def word_stats(word: tuple[int,...]) -> tuple[int,int,int,int]:
    stack=[]
    for x in reversed(word):
        if x==-1:
            stack.append((0,0,0,0))
        else:
            left=stack.pop()
            right=stack.pop()
            stack.append(merge(left,right))
    require(len(stack)==1, 'invalid tree word')
    return stack[0]


def main() -> None:
    root=Path(__file__).resolve().parents[1]
    (root/'data').mkdir(exist_ok=True)
    max_n=11
    rows=[]
    checked=0
    for n in range(1,max_n+1):
        av=avoiders(n)
        require(len(av)==catalan(n), f'Catalan count at {n}')
        require(len(set(av))==len(av),f'duplicate permutation at {n}')
        dist=Counter()
        first=Counter()
        last=Counter()
        for p in av:
            i=p.index(n)
            b=n-i-1
            left=tuple(x-b for x in p[:i])
            right=p[i+1:]
            s=stats(p)
            require(merge(stats(left),stats(right))==s, f'root identity {p}')
            dist[n-s[3]]+=1
            first[p[0]]+=1
            last[p[-1]]+=1
        if n<=8:
            direct={p for p in permutations(range(1,n+1)) if avoids_132(p)}
            require(direct==set(av),f'independent avoidance test {n}')
        for f in range(1,n+1):
            expected=Fraction(n-f+1,n)*comb(n+f-2,n-1)
            require(first[f]==expected,f'first count at {n},{f}')
            require(last[f]==catalan(n-f)*catalan(f-1),f'last count at {n},{f}')
        for d in range(1,n+1):
            h=min(d,(n-1)//2)
            stail=Fraction(2*(h+1)*(2*h+1),h+2)*Fraction(catalan(h),4**h)
            tail=Fraction(sum(c for k,c in dist.items() if k>=d),catalan(n))
            require(tail<=stail,f'tail envelope at {n},{d}')
        for k,c in sorted(dist.items()):
            rows.append([n,k,c,catalan(n)])
        checked+=len(av)
    # Exact tail identity and weighted-cost normalization telescoping.
    for h in range(101):
        partial=sum(Fraction(catalan(t+1)-2*catalan(t),4**t)
                    for t in range(1,h+1))
        tail=Fraction(2*(h+1)*(2*h+1),h+2)*Fraction(catalan(h),4**h)
        require(partial+tail==1,f'cost tail identity {h}')
    # Exhaustive uniformity check of the sampler's cycle-lemma map.
    from itertools import combinations
    sampler_checks=0
    for n in range(1,7):
        multiplicities=Counter()
        hist=Counter()
        for positions in combinations(range(2*n+1),n):
            positives=set(positions)
            w=tuple(1 if i in positives else -1 for i in range(2*n+1))
            t=cycle_tree(w)
            multiplicities[t]+=1
        require(len(multiplicities)==catalan(n),f'cycle output count {n}')
        require(set(multiplicities.values())=={2*n+1},f'cycle uniformity {n}')
        for w in multiplicities:
            hist[word_stats(w)]+=1
        require(hist==Counter(stats(p) for p in avoiders(n)),f'sampler stats {n}')
        sampler_checks+=comb(2*n+1,n)
    with (root/'data'/'exact_small_distributions.csv').open('w',newline='') as f:
        wr=csv.writer(f); wr.writerow(['n','deficit','count','catalan_total']); wr.writerows(rows)
    report={'status':'PASS','exact_avoiders_checked':checked,'sizes':f'1..{max_n}',
            'independent_132_filter_sizes':'1..8','cost_tail_checks':101,
            'cycle_lemma_words_checked':sampler_checks,'cycle_lemma_sizes':'1..6',
            'claims':'Finite root identities, endpoint formulas, tail bounds, sampler uniformity; no asymptotic certification.'}
    (root/'data'/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
