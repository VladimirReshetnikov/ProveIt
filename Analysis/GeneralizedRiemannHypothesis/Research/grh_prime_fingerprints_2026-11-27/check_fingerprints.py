#!/usr/bin/env python3
"""Exact finite wildcard/error/erasure list-size check (standard library only).

This verifies the finite example, not GRH or the asymptotic theorem.
All possible erased sets and received words are covered by enumeration of
balls around each character. Each character contributes once per word.
"""
import argparse
from collections import Counter
from itertools import combinations
from math import isqrt
from random import Random
import json


def squarefree(n):
    n = abs(n)
    return n > 0 and all(n % (p*p) for p in range(2, isqrt(n)+1))


def fundamental(D):
    return D != 0 and ((D % 4 == 1 and squarefree(D)) or
        (D % 4 == 0 and (D//4) % 4 in (2, 3) and squarefree(D//4)))


def primes(lo, hi):
    return [p for p in range(max(lo,3),hi+1) if all(p%d for d in range(2,isqrt(p)+1))]


def sign(D, p):
    a = D % p
    return 0 if a == 0 else 1 if pow(a,(p-1)//2,p)==1 else -1


def masks(pos, radius):
    for j in range(min(radius,len(pos))+1):
        for inds in combinations(pos,j):
            yield sum(1<<i for i in inds)


def check(Q, ps, e, t):
    assert 0 <= e < len(ps) and t >= 0
    ds = [D for D in range(-Q,Q+1) if fundamental(D)]
    signs = [[sign(D,p) for p in ps] for D in ds]
    best = -1
    witness = None
    hist = Counter()
    for k in range(e+1):
        for erased in combinations(range(len(ps)),k):
            keep = [i for i in range(len(ps)) if i not in erased]
            count = Counter()
            for row in signs:
                base = sum(1<<j for j,i in enumerate(keep) if row[i]==-1)
                wild = [j for j,i in enumerate(keep) if row[i]==0]
                known = [j for j,i in enumerate(keep) if row[i]!=0]
                # Disjoint supports: each word has exactly one representation.
                for w in masks(wild,len(wild)):
                    for err in masks(known,t):
                        count[base ^ w ^ err] += 1
            # Words not in the counter have list size zero.
            hist.update(count.values())
            hist[0] += (1<<len(keep))-len(count)
            word,m = max(count.items(),key=lambda pair:pair[1])
            if m > best:
                best = m
                y = [(-1 if word>>j&1 else 1) for j in range(len(keep))]
                candidates = [D for D,row in zip(ds,signs) if
                    sum(row[i]!=0 and row[i]!=v for i,v in zip(keep,y))<=t]
                assert len(candidates)==m
                witness = {'erased_indices_zero_based':list(erased),'received_signs':y,
                           'candidate_discriminants':candidates}
    from math import comb
    assert sum(hist.values())==sum(comb(len(ps),k)*2**(len(ps)-k) for k in range(e+1))
    return {'Q':Q,'primes':ps,'number_of_characters':len(ds),'max_erasures':e,
            'max_errors_absolute':t,'maximum_list_size':best,
            'histogram_all_erased_sets_and_words':dict(sorted(hist.items())),
            'witness':witness}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--Q',type=int,default=128)
    p.add_argument('--n',type=int,default=16)
    p.add_argument('--lo',type=int,default=101)
    p.add_argument('--hi',type=int,default=300)
    p.add_argument('--erasures',type=int,default=2)
    p.add_argument('--errors',type=int,default=2)
    p.add_argument('--seed',type=int,default=271126)
    args=p.parse_args()
    ps=sorted(Random(args.seed).sample(primes(args.lo,args.hi),args.n))
    print(json.dumps(check(args.Q,ps,args.erasures,args.errors),indent=2))

if __name__=='__main__': main()
