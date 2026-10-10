#!/usr/bin/env python3
"""Exact finite audits, independent ideal-rank checks, and Hilbert tables."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
from math import gcd
from pathlib import Path
import json,time,argparse
import depth_projector as P
from cayley_filtered_counts import generators,hilbert

def primitive(row):
    row={w:int(c) for w,c in row.items() if c}
    if not row:return {}
    g=0
    for c in row.values():g=gcd(g,c)
    if row[min(row)]<0:g=-g
    return {w:c//g for w,c in row.items()}

def rank_exact(rows,keep=None):
    pivots={}
    for rr in rows:
        row=primitive({w:c for w,c in rr.items() if keep is None or keep(w)})
        while row:
            w=min(row)
            if w not in pivots:
                pivots[w]=row;break
            piv=pivots[w];a,b=row[w],piv[w];g=gcd(a,b)
            z={v:c*(b//g) for v,c in row.items()}
            for v,c in piv.items():z[v]=z.get(v,0)-c*(a//g)
            row=primitive(z)
    return len(pivots)

def ideal_rows(n):
    ad={0:[()]}
    for k in range(1,n+1):ad[k]=[w for w in product(range(5),repeat=k) if P.admissible(w)]
    seen=set();out=[]
    for k in range(1,n+1):
        for u in ad[k]:
            r=P.add({u:1},P.cayley(u),-1)
            if not r:continue
            for v in ad[n-k]:
                if (P.parity(u)+P.parity(v))%2!=1:continue
                row=primitive(P.multiply(r,{v:1}))
                key=tuple(sorted(row.items()))
                if key and key not in seen:out.append(row);seen.add(key)
    return ad[n],out

def verify(N=4):
    start=time.monotonic();word_checks={};cut_checks=0;products=0
    for n in range(1,N+1):
        for w in product(range(5),repeat=n):
            r=P.regularize(w);assert P.apply(P.regularize,r)==r
            assert P.apply(P.cayley,r)==P.apply(P.regularize,P.cayley(w))
            assert all(P.degree(v)==P.degree(w) for v in r)
            if P.admissible(w):assert r=={w:1}
            e=P.eulerian(w);assert e==P.eulerian_by_cuts(w);cut_checks+=1
            e0=P.lift(w);assert all(P.degree(v)==P.degree(w) for v in e0)
            if P.admissible(w):assert P.apply(P.lift,e0)==e0
            p=P.projection(w)
            assert all(P.admissible(v) and P.depth(v)<=P.depth(w) for v in p)
            assert p==P.apply(P.projection,p)
            assert p==P.apply(P.projection,P.cayley(w))
            assert p==P.apply(P.projection,r)
            assert P.apply(P.conjugate,p)==P.apply(P.projection,P.conjugate(w))
        word_checks[str(n)]=5**n
    for n in range(2,N+1):
        for k in range(1,n):
            for u in product(range(5),repeat=k):
                for v in product(range(5),repeat=n-k):
                    assert P.apply(P.projection,P.shuffle(u,v))==P.multiply(P.projection(u),P.projection(v))
                    products+=1
    gs,h=hilbert(max(10,N));ranks=[]
    for n in range(1,N+1):
        basis,rows=ideal_rows(n);basis=[w for w in basis if P.parity(w)]
        rank=rank_exact(rows)
        for d in range(1,n+1):
            raw=sum(P.depth(w)<=d for w in basis)
            projected_rank=rank_exact(rows,lambda w:P.depth(w)>d)
            intersection=rank-projected_rank
            actual=raw-intersection
            expected=sum(h.get((n,j,1),0) for j in range(d+1))
            assert actual==expected,(n,d,actual,expected)
            ranks.append({'weight':n,'depth_bound':d,'ambient_odd':raw,
                          'ideal_intersection_rank':intersection,'quotient_image_dimension':actual})
    # The oriented image is intentionally not pointwise C-invariant.
    example=(P.Z,P.Y)
    assert P.projection(example)=={example:1}
    assert P.apply(P.cayley,P.projection(example))!=P.projection(example)
    # At fixed nonzero excess, the direct Cayley example has depth-one normal form.
    for n in range(2,8):
        assert P.projection((P.Y,)+(P.X,)*(n-1))=={(P.Z,)*(n-1)+(P.Y,):1}
    return {'result':'PASS','word_checks':word_checks,'consecutive_cut_eulerian_checks':cut_checks,
            'shuffle_multiplicativity_checks':products,'independent_exact_ideal_ranks':ranks,
            'weight7_odd_graded_depth_dimensions':[h.get((7,d,1),0) for d in range(1,8)],
            'weight7_odd_total':sum(h.get((7,d,1),0) for d in range(1,8)),
            'hilbert_odd_depth_table':{str(n):[h.get((n,d,1),0) for d in range(1,n+1)] for n in range(1,11)},
            'non_pointwise_C_invariant_example':{'input':'ZY','projection':'ZY','C_projection':'YX'},
            'arithmetic':'integers and fractions only; independent rank elimination is fraction-free over Z',
            'elapsed_seconds':round(time.monotonic()-start,3)}
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--max-weight',type=int,default=4);ap.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'verification'/'depth_projector_verification.json');a=ap.parse_args()
    data=verify(a.max_weight);a.output.write_text(json.dumps(data,indent=2)+'\n');print(json.dumps(data,indent=2))
