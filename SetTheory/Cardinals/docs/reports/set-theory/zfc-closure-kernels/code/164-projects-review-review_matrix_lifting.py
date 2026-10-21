#!/usr/bin/env python3
"""Independent numerical replay accompanying the universal matrix-lifting review.

No author checker imports. Finite tests supplement, but do not prove, the
universal recursion/context argument in matrix-lifting-independent-review.md.
"""
import argparse,json,sys
from pathlib import Path
from itertools import product
from functools import cache

M=((3,3,2,3),(3,3,3,3),(0,3,3,3),(0,1,2,3))

def pair(a,b):return (a+b)*(a+b+1)//2+b

def inverse(n):
    # Independent binary search, not the author's square-root inverse.
    lo,hi=0,n+1
    while lo+1<hi:
        mid=(lo+hi)//2
        if mid*(mid+1)//2<=n:lo=mid
        else:hi=mid
    b=n-lo*(lo+1)//2
    return lo-b,b

def child(n):return inverse(n//4)

def native_imp(a,b):return 4*pair(a,b)

def rho(a,b,c,u,f):return f(f(f(c,u),a),f(f(a,c),f(b,c)))

@cache
def h(n):
    if n<4:return (3,0,1,2)[n]
    l,r=child(n)
    assert 0<=l<n and 0<=r<n
    return M[h(l)][h(r)]

def project(a,word):
    for x in word:a=child(a)[x=='R']
    return a

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    if not __debug__ or sys.flags.optimize:raise RuntimeError('Assertions must be enabled')
    imply=lambda a,b:M[a][b]
    homo=0
    for a,b in product(range(96),repeat=2):
        assert inverse(pair(a,b))==(a,b)
        assert h(native_imp(a,b))==imply(h(a),h(b));homo+=1
    checked=0;escape=0;words=('','L','R','RRR')
    for a in range(8192):
        for word in words:
            at=a;low=False
            for letter in word:
                if at in(1,2,3):low=True
                at=child(at)[letter=='R']
            if low:
                assert at==0;escape+=1
            for b,c in product(range(4),repeat=2):
                assert rho(h(a),b,c,h(at),imply)==3;checked+=1
    constant=0
    for a,b,c in product(range(4),repeat=3):
        assert rho(a,b,c,3,imply)==3;constant+=1
    witness=rho(2,1,3,1,native_imp)
    assert witness==2526379112 and h(witness)==2 and h(1)==0
    result={'status':'INDEPENDENT_TOTAL_RAW_PROJECTOR_LIFT_REVIEW_PASS','matrix':M,'seeds':[3,0,1,2],
            'implication_homomorphism_cases':homo,'homomorphism_domain':'0<=a,b<96',
            'raw_family_cases':checked,'raw_family_domain':'0<=A<8192; arbitrary matrix values B,C; four words epsilon,L,R,RRR',
            'proper_prefix_low_seed_escape_cases':escape,'constant_truth_family_cases':constant,
            'unrestricted_raw_witness':{'A':2,'B':1,'C':3,'U':1,'code':witness,'value':h(witness)},
            'scope':'Finite exact arithmetic checks plus separately reviewed universal lifting argument. Models truth/MP and constant0,epsilon,L,R,RRR rho8 families (and I,K,Peirce,cd59 via homomorphism); not the full native calculus, GEN, or bundle. No failure of ZFC equiconsistency or machine lower bound is claimed.'}
    args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
