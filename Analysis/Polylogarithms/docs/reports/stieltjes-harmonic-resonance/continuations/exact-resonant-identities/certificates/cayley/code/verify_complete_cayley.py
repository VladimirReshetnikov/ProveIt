#!/usr/bin/env python3
"""Replay the full-Cayley extension of the exact S6 obstruction.

Only Python's standard library is required. All mathematical arithmetic
uses integers or fractions. No cached matrix, rank assumption, modular
arithmetic, numerical polylogarithm or integer-relation search is used.
"""
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from itertools import permutations,product
from math import comb,lcm
from pathlib import Path
import argparse,hashlib,json,time,sys
sys.dont_write_bytecode=True
import depth_projector as P
import bounded_relations as R

ROOT=Path(__file__).resolve().parents[1]
EXPECTED_SHA256={
    'code/depth_projector.py':'bfd84d6a6713e210b968e1d2b9bbf1cf4a2cf6805ac93f42e4ea373488dba367',
    'code/bounded_relations.py':'044eadc2fccbc850c155a4c9d458df7061cbd9aaa2bd6852339e9aea6cde4512',
    'data/separator.json':'bfafe9723a955217a164603959ea8bef0ca64117d2375f74cbac693641062f8f',
}

@lru_cache(None)
def permutation_integers(n):
    """The source Eulerian sum, with one exact common denominator."""
    den=lcm(*(n*comb(n-1,d) for d in range(n)))
    terms=[]
    for p in permutations(range(n)):
        inv=[0]*n
        for i,j in enumerate(p):inv[j]=i
        d=sum(inv[j]>inv[j+1] for j in range(n-1))
        terms.append((p,(-1)**d*(den//(n*comb(n-1,d)))))
    return den,terms

@lru_cache(None)
def integer_eulerian(w):
    if not w:return {}
    den,terms=permutation_integers(len(w));out=defaultdict(int)
    for p,c in terms:out[tuple(w[j] for j in p)]+=c
    return {w:Q(c,den) for w,c in out.items() if c}

# This is exactly the formula in the pinned implementation, but repeated
# copies of the same word are accumulated as integers before division.
# Its comparison with the independent consecutive-cut definition is
# included below for every word of weights one through four.
P.eulerian=integer_eulerian

@lru_cache(None)
def change_basis(w):
    """Raw Z=-1,C=0,A=1,B=2,ABAR=3 to adapted Z,Y,H,B,X."""
    table={-1:{P.Z:1},0:{P.X:1,P.B:1},
           1:{P.Y:Q(1,2),P.H:Q(1,2),P.B:Q(1,2)},
           2:{P.B:1},3:{P.Y:Q(-1,2),P.H:Q(1,2),P.B:Q(1,2)}}
    out={():Q(1)}
    for a in w:
        nxt={}
        for u,c in out.items():
            for b,d in table[a].items():nxt[u+(b,)]=c*d
        out=nxt
    return out

def audit_projector():
    """Independent finite convention checks; not the all-weight proof."""
    words=0;products=0
    for n in range(1,5):
        for w in product(range(5),repeat=n):
            reg=P.regularize(w)
            assert P.apply(P.regularize,reg)==reg
            assert P.apply(P.cayley,reg)==P.apply(P.regularize,P.cayley(w))
            assert all(P.degree(v)==P.degree(w) for v in reg)
            if P.admissible(w):assert reg=={w:1}
            assert integer_eulerian(w)==P.eulerian_by_cuts(w)
            lifted=P.lift(w)
            assert all(P.degree(v)==P.degree(w) for v in lifted)
            if P.admissible(w):assert P.apply(P.lift,lifted)==lifted
            proj=P.projection(w)
            assert all(P.admissible(v) and P.depth(v)<=P.depth(w) for v in proj)
            assert P.apply(P.projection,proj)==proj
            assert P.apply(P.projection,P.cayley(w))==proj
            assert P.apply(P.projection,reg)==proj
            assert P.apply(P.conjugate,proj)==P.apply(P.projection,P.conjugate(w))
            words+=1
    for n in range(2,5):
        for k in range(1,n):
            for u in product(range(5),repeat=k):
                for v in product(range(5),repeat=n-k):
                    lhs=P.apply(P.projection,P.shuffle(u,v))
                    rhs=P.multiply(P.projection(u),P.projection(v))
                    assert lhs==rhs
                    products+=1
    assert words==780 and products==2150
    return {'words_through_weight_four':words,'shuffle_products_through_weight_four':products,
            'independent_consecutive_cut_eulerian_checks':words}

def verify():
    started=time.monotonic()
    for name,digest in EXPECTED_SHA256.items():
        actual=hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
        assert actual==digest,('File integrity failure',name,actual)
    data=json.loads((ROOT/'data'/'separator.json').read_text())
    assert data['weight']==7 and data['maximum_depth']==4
    coords=[w for w in product(range(5),repeat=7)
            if P.admissible(w) and P.depth(w)<=4 and P.parity(w)]
    assert len(coords)==data['ambient_dimension']==2546
    assert len({i for i,c in data['functional']})==len(data['functional'])
    assert all(0<=i<len(coords) and isinstance(c,int) and c for i,c in data['functional'])
    ell={coords[i]:c for i,c in data['functional']}
    def pair_adapted(poly):return sum(c*ell.get(w,0) for w,c in poly.items())
    @lru_cache(None)
    def raw_coefficient(w):return pair_adapted(change_basis(w))
    def pair_raw(poly):return sum(c*raw_coefficient(w) for w,c in R.compress(poly).items())

    audits=audit_projector()
    print('Projector conventions and small independent audits: PASS',flush=True)
    family,counts=R.complete_family()
    assert counts==data['row_counts'] and len(family)==sum(counts.values())==5131
    max_row_support=0
    for row in family:
        assert row and all(len(w)==7 and w[0]!=0 and w[-1]!=-1
                           and sum(a!=-1 for a in w)<=4 for w,c in row)
        assert pair_raw(dict(row))==0
        max_row_support=max(max_row_support,len(row))
    print('All 5,131 independently regenerated inherited rows: PASS',flush=True)

    nonzero=0
    for k,w in enumerate(coords):
        proj=P.projection(w)
        assert all(P.admissible(v) and len(v)==7 and P.depth(v)<=P.depth(w)
                   and P.parity(v) for v in proj)
        assert pair_adapted(proj)==ell.get(w,0),w
        nonzero+=proj!={w:1}
        if (k+1)%500==0:print('Full-ideal basis checks:',k+1,'/',len(coords),flush=True)
    target=R.target()
    assert all(len(w)==7 and w[0]!=0 and w[-1]!=-1
               and sum(a!=-1 for a in w)<=2 for w in target)
    pairing=pair_raw(target)
    assert pairing==data['target_pairing'] and pairing!=0
    receipt={'result':'PASS','source_integrity':'SHA-256 matches',
             'ambient_adapted_odd_dimension':len(coords),'functional_support':len(ell),
             'inherited_rows_regenerated':len(family),'row_counts':counts,
             'complete_cayley_basis_checks':len(coords),'nonzero_projector_difference_rows':nonzero,
             'target_normalization':128588,'target_pairing':int(pairing),
             'maximum_inherited_row_support':max_row_support,'projector_audits':audits,
             'arithmetic':'integers and exact fractions only',
             'conclusion':'Target is outside the full Cayley shuffle ideal plus the inherited bounded finite relation span.',
             'period_status':'The numerical S6 equality remains conjectural.',
             'elapsed_seconds':round(time.monotonic()-started,3)}
    return receipt

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--receipt',type=Path,default=ROOT/'verification.json')
    args=ap.parse_args();receipt=verify()
    args.receipt.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
