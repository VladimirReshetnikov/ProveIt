#!/usr/bin/env python3
"""Rebuild the 96-term convergent Cayley identity for S6 exactly."""
import json
from itertools import product
from collections import Counter
from check_cayley_ranks import Z,C,A,B,D,cayley,project,words

def right(p):
    r=Counter()
    for tail in product((C,B),repeat=p-1):
        sign=(-1)**tail.count(B)
        r[(B,A)+tail]+=2*sign
        r[(A,A)+tail]-=sign
        r[(A,D)+tail]+=sign
    return dict(r)

def check(p):
    lhs={(Z,)*(p-1)+(A,A):1,(Z,)*(p-1)+(A,D):1}
    transformed=Counter()
    for w,c in lhs.items():
        for v,m in cayley(w).items():transformed[v]+=c*m
    residual=Counter(project(transformed,'odd'))
    for w,c in project(right(p),'odd').items():residual[w]-=c
    assert not {w:c for w,c in residual.items() if c}
    for w in right(p):assert w[0]!=C and w[-1]!=Z
    return {'p':p,'weight':p+1,'right_side_words':len(right(p)),
            'right_side_depth':p+1,'exact_residual_coordinates':0}

def main():
    receipt={'result':'PASS','checks':[check(p) for p in range(1,9)],
             'arithmetic':'integers; no numerical polylogarithms'}
    print(json.dumps(receipt,indent=2))
    with open('harmonic_cayley_verified.json','w') as f:json.dump(receipt,f,indent=2);f.write('\n')
    naming={Z:'z',C:'c',A:'a',B:'b',D:'abar'}
    expansion={'schema':'proveit.convergent-harmonic-cayley.v1','p':6,
               'meaning':'Imaginary part of the linear combination of convergent outer-first iterated integrals at 1',
               'letters':{'z':'dt/t','c':'dt/(1-t)','a':'i dt/(1-i t)','b':'-dt/(1+t)','abar':'-i dt/(1+i t)'},
               'unexpanded_right':'(2 b a - a a + a abar)(c-b)^5',
               'rows':[{'coefficient':c,'word':[naming[x] for x in w]} for w,c in sorted(right(6).items())]}
    with open('S6_cayley_depth_seven.json','w') as f:json.dump(expansion,f,indent=2);f.write('\n')
if __name__=='__main__':main()
