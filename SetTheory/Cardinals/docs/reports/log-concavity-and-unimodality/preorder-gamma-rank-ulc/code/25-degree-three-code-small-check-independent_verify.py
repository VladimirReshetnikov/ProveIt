#!/usr/bin/env python3
"""Independent Hall-subset verifier for exact C++ enumeration certificates."""
from itertools import permutations
from collections import defaultdict
from functools import lru_cache
from math import comb
from pathlib import Path
import csv,json
ROOT=Path(__file__).resolve().parent

def preorder(rows):
    rr=[r|1<<i for i,r in enumerate(rows)]
    return all(not(rr[j]&~rr[i]) for i,r in enumerate(rr) for j in range(len(rr)) if r>>j&1)

@lru_cache(None)
def support_pairs(n):
    masks=defaultdict(list)
    for a in range(1<<n):masks[a.bit_count()].append(a)
    return [(k,a,b) for k in range(1,n//2+1) for a in masks[k] for b in masks[k] if not a&b]

def gamma_hall(rows):
    # Hall's condition independently tests every nonempty subset of the source set.
    n=len(rows)
    union=[0]*(1<<n)
    for s in range(1,1<<n):
        bit=s&-s
        union[s]=union[s^bit]|rows[bit.bit_length()-1]
    g=[1]+[0]*(n//2)
    for k,a,b in support_pairs(n):
        s=a
        while s:
            if (union[s]&b).bit_count()<s.bit_count():break
            s=(s-1)&a
        else:g[k]+=1
    return g

def matching_degree(rows):
    n=len(rows)
    @lru_cache(None)
    def opt(s):
        if not s:return 0
        bit=s&-s;i=bit.bit_length()-1;rem=s^bit
        best=opt(rem)
        for j in range(n):
            if rem>>j&1 and (rows[i]>>j&1 or rows[j]>>i&1):
                best=max(best,1+opt(rem^(1<<j)))
        return best
    return opt((1<<n)-1)

records=list(csv.DictReader((ROOT/'gamma_representatives.csv').open()))
checked=defaultdict(int)
for rec in records:
    n=int(rec['n']);rows=tuple(map(int,rec['rowmasks'].split()));assert len(rows)==n
    assert all(not(r>>i&1) for i,r in enumerate(rows))
    assert preorder(rows),rec
    g=gamma_hall(rows);expected=[int(rec[f'g{k}']) for k in range(4)]
    assert (g+[0]*4)[:4]==expected,(rec,g)
    assert len(g)<5 or g[4]==0,(rec,g)
    deg=max(k for k,v in enumerate(g) if v)
    assert matching_degree(rows)==deg,(rec,g)
    if deg==2:
        assert g[1]*g[1]>=4*g[2]
    if deg==3:
        _,a,b,c=g[:4]
        assert a*a>=3*b and b*b>=3*a*c
        assert a*a*b*b-4*b*b*b-4*a*a*a*c-27*c*c+18*a*b*c>=0
    checked[n]+=1
print('Hall and undirected-matching cross-checks:',dict(checked),flush=True)

# Direct enumeration of all reflexive directed relations for n<=4.
# No quotient or natural labeling is used here.
direct={};direct_counts={}
for n in range(1,5):
    es=[(i,j) for i in range(n) for j in range(n) if i!=j]
    all_preorders=set()
    for mask in range(1<<len(es)):
        rows=[0]*n
        for e,(i,j) in enumerate(es):
            if mask>>e&1:rows[i]|=1<<j
        if preorder(rows):all_preorders.add(tuple(rows))
    direct[n]=all_preorders;direct_counts[n]=len(all_preorders)
    observed={tuple((gamma_hall(r)+[0]*4)[:4]) for r in all_preorders}
    recorded={tuple(int(r[f'g{k}'])for k in range(4))for r in records if int(r['n'])==n}
    assert observed==recorded
assert direct_counts=={1:1,2:4,3:29,4:355},direct_counts
print('Direct labeled preorder counts:',direct_counts,flush=True)

def compositions(n,m):
    if m==1:yield(n,);return
    for a in range(1,n-m+2):
        for tail in compositions(n-a,m-1):yield(a,)+tail

def natural_posets(m):
    # Independent mask-filter generator, rather than C++'s ideal extension generator.
    es=[(i,j)for i in range(m)for j in range(i+1,m)]
    for mask in range(1<<len(es)):
        rr=[0]*m
        for e,(i,j) in enumerate(es):
            if mask>>e&1:rr[i]|=1<<j
        if preorder(rr):yield rr

for n in range(1,5):
    expanded=set()
    for m in range(1,n+1):
        for q in natural_posets(m):
            for blocks in compositions(n,m):
                cls=[i for i,sz in enumerate(blocks)for _ in range(sz)]
                rows=[sum(1<<j for j in range(n) if j!=i and(cls[i]==cls[j]or q[cls[i]]>>cls[j]&1))for i in range(n)]
                for p in permutations(range(n)):
                    rr=[0]*n
                    for i in range(n):
                        for j in range(n):
                            if rows[i]>>j&1:rr[p[i]]|=1<<p[j]
                    expanded.add(tuple(rr))
    assert expanded==direct[n],n
print('Quotient/block generation covers exactly every labeled preorder through n=4',flush=True)

for n in range(1,8):
    rows=[((1<<n)-1)^(1<<i)for i in range(n)]
    assert gamma_hall(rows)==[comb(n,k)*comb(n-k,k)for k in range(n//2+1)]
print('Complete preorder closed-form check passed through n=7')
result={'representatives_verified_by_hall':dict(checked),'labeled_preorders_directly_verified':direct_counts,'quotient_coverage_directly_verified_through_n':4,'complete_preorder_formula_verified_through_n':7,'all_passed':True}
(ROOT/'independent_verification.json').write_text(json.dumps(result,indent=2)+'\n')
