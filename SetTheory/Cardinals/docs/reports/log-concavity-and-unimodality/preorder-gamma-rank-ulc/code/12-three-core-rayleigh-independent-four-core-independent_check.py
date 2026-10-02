#!/usr/bin/env python3
"""Independent Hall-support and integer SOS verification; standard library only."""
from itertools import combinations
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
import json

OUT=Path(__file__).resolve().parent
N=[set('cde'),set('abe'),set('bd'),set('e')]
HEADS='abcde'

def subsets(items):
    return (s for k in range(len(items)+1) for s in combinations(items,k))

def feasible(tails,heads):
    H=set(heads)
    for J in subsets(tails):
        neighbors=set().union(*(N[t] for t in J))
        if len(neighbors&H)<len(J):return False
    return True

def B(tails):
    return {''.join(H):1 for H in combinations(HEADS,len(tails)) if feasible(tails,H)}

def add(P,Q,scale=1):
    R=dict(P)
    for m,c in Q.items():R[m]=R.get(m,0)+scale*c
    return {m:c for m,c in R.items() if c}

def mul(P,Q):
    R=defaultdict(int)
    for m,c in P.items():
        for n,d in Q.items():R[''.join(sorted(m+n))]+=c*d
    return {m:c for m,c in R.items() if c}

def main():
    bs={str(J):B(J) for J in [(0,1,2),(0,1,3),(0,1),(0,1,2,3)]}
    expected=[set('abc abd abe acd ade bcd bce bde cde'.split()),
              set('ace ade bce bde'.split()),
              set('ac ad ae bc bd be ce de'.split()),
              set('abce abde acde bcde'.split())]
    for P,E in zip(bs.values(),expected):assert set(P)==E and set(P.values())=={1}
    p,q,r,s=bs.values()
    gap=add(mul(p,q),mul(r,s),-1)
    assert gap=={'aaddee':1,'abcdee':-1,'abddee':1,
                 'bbccee':1,'bbcdee':1,'bbddee':1}
    # Denominator-cleared identity: 4*gap=e^2[(2ad-bc+bd)^2+3(bc+bd)^2].
    Q1={'ad':2,'bc':-1,'bd':1};Q2={'bc':1,'bd':1}
    sos4=mul({'ee':1},add(mul(Q1,Q1),mul(Q2,Q2),3))
    assert sos4=={m:4*c for m,c in gap.items()}
    cover_tail={0,1};cover_head=set('bde')
    assert all(t in cover_tail or h in cover_head for t in range(4) for h in N[t])
    fullmatching={0:'c',1:'a',2:'b',3:'e'}
    assert len(set(fullmatching.values()))==4
    assert all(h in N[t] for t,h in fullmatching.items())
    gamma=[sum(len(B(J)) for J in combinations(range(4),k)) for k in range(5)]
    assert gamma==[1,9,24,19,4]
    def value(x):return sum(c*x**k for k,c in enumerate(gamma))
    intervals=[(-3,-2),(-2,-1),(Fraction(-1,3),Fraction(-1,4)),(Fraction(-1,4),0)]
    assert all(value(a)*value(b)<0 for a,b in intervals)
    # Four disjoint negative sign-change intervals give all four roots exactly.
    receipt={'verdict':'PASS','method':'Hall conditions, independent squarefree support sets, integer-cleared SOS',
             'basis_polynomials':bs,'basis_counts':[len(P) for P in bs.values()],
             'gap':dict(sorted(gap.items())),'negative_monomial':'abcdee','negative_coefficient':-1,
             'integer_cleared_SOS':'4*gap=e^2*((2*a*d-b*c+b*d)^2+3*(b*c+b*d)^2)',
             'role_cover_verified':{'tails':[0,1],'heads':['b','d','e']},
             'degree_four_matching':fullmatching,'unit_activity_gamma':gamma,
             'unit_activity_negative_root_intervals':[[str(a),str(b)] for a,b in intervals],
             'scope':'Failure of coefficientwise four-core boundary extension; this gap is nonnegative for all real head activities'}
    (OUT/'independent_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
