#!/usr/bin/env python3
"""Exact polynomial and finite-support certificates for flexible equality binders.

No third-party dependencies. Numeric samples are not used for the all-natural
claim. Polynomial identities are exact over Q. For s=a+b=t+1>0, a=t+1-b;
nonnegative coefficients with positive constant prove both fresh inequalities.
The s=0 case forces a=b=0 and is handled explicitly.

The semantic finite model test is complete for this specific equality-only row:
only four index names a,b,c,r and four values (at a,b,c and quantified d) matter.
Every larger structure restricts to the same equality pattern of these values.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import argparse,json

# Sparse polynomials in t,b. Exponents index tuples.
def add(*ps):
    q={}
    for p in ps:
        for mon,v in p.items(): q[mon]=q.get(mon,F(0))+F(v)
    return {m:v for m,v in q.items() if v}
def mul(p,q):
    out={}
    for (i,j),v in p.items():
        for (k,l),w in q.items():
            m=(i+k,j+l);out[m]=out.get(m,F(0))+v*w
    return {m:v for m,v in out.items() if v}
def scale(v,p): return {m:F(v)*c for m,c in p.items() if v*c}
def sub(p,q): return add(p,scale(-1,q))
def constant(v): return {(0,0):F(v)} if v else {}
def jsonpoly(p): return {f't^{i} b^{j}':str(v) for(i,j),v in sorted(p.items())}
ONE=constant(1);T={(1,0):F(1)};B={(0,1):F(1)}
S=add(T,ONE);A=sub(S,B)
P=add(scale(F(1,2),mul(S,add(S,ONE))),B)
functions={'2P':scale(2,P),'4P':scale(4,P),'P+1':add(P,ONE),
           '4P+1':add(scale(4,P),ONE),'4P+2':add(scale(4,P),constant(2)),
           '4P+3':add(scale(4,P),constant(3))}
expected={
'2P':[{(2,0):1,(1,0):2,(0,0):1,(0,1):3},
       {(2,0):1,(1,0):3,(0,0):2,(0,1):1}],
'4P':[{(2,0):2,(1,0):5,(0,0):3,(0,1):5},
       {(2,0):2,(1,0):6,(0,0):4,(0,1):3}],
'P+1':[{(2,0):F(1,2),(1,0):F(1,2),(0,0):1,(0,1):2},
        {(2,0):F(1,2),(1,0):F(3,2),(0,0):2}]
}
arithmetic={}
for name,fp in functions.items():
    deltas=[sub(fp,A),sub(fp,B)]
    if name in expected: assert deltas==expected[name],(name,deltas)
    assert all(all(v>=0 for v in q.values()) and q.get((0,0),F(0))>0 for q in deltas)
    arithmetic[name]={'positive_case':{'substitution':'a+b=t+1; a=t+1-b; t,b>=0',
                        'f-a':jsonpoly(deltas[0]),'f-b':jsonpoly(deltas[1])},
                      'zero_case':'a=b=0; diagonal always permitted'}
# Sum-plus-one uses independent original variables a,b, not the t,b basis.
sum_f=add(T,B,ONE)
sum_deltas=[sub(sum_f,T),sub(sum_f,B)]
assert sum_deltas==[add(B,ONE),add(T,ONE)]
assert all(all(v>=0 for v in q.values()) and q[(0,0)]>0 for q in sum_deltas)
arithmetic['a+b+1']={'all_cases':{'variables':'t denotes a; a,b>=0',
                                      'f-a':jsonpoly(sum_deltas[0]),'f-b':jsonpoly(sum_deltas[1])}}
# Exact counterexample to bare P: P(1,0)=1.
assert (1+0)*(1+0+1)//2+0==1

# Restricted-growth strings enumerate equality patterns of four literal labels.
def patterns(n,p=()):
    if len(p)==n:
        yield p; return
    for x in range(1+(max(p)+1 if p else 0)):
        yield from patterns(n,p+(x,))
label_patterns=list(patterns(4))
assert len(label_patterns)==15
semantic=[];total=0
for labels in label_patterns:
    a,b,c,r=labels;k=max(labels)+1
    expected_valid=(a==b or (r!=a and r!=b))
    witness=None;cases=0
    for values in product(range(4),repeat=k):
        antecedent=values[c]==values[a] and values[c]==values[b]
        for d in range(4):
            av=d if a==r else values[a]
            bv=d if b==r else values[b]
            valid=(not antecedent) or av==bv
            cases+=1
            if not valid and witness is None:witness={'assignment':values,'quantified_value':d}
    assert (witness is None)==expected_valid,labels
    semantic.append({'labels_abr':{'a':a,'b':b,'c':c,'r':r},
                     'fresh_off_diagonal':expected_valid,'valid':witness is None,
                     'complete_finite_cases':cases,'counterexample':witness})
    total+=cases
result={'status':'EXACT_BINDER_CERTIFICATES_PASS','arithmetic':arithmetic,
        'semantic_scope':{'label_patterns':15,'domain_representatives':4,
                          'complete_cases':total,
                          'covering_lemma':'Only equality of a,b,c,r labels and at most four values at a,b,c,d affects G_f.'},
        'semantic_cases':semantic,
        'not_claimed':['A proof-assistant endpoint','A binary runtime theorem','A smaller state count']}
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args();args.output.parent.mkdir(parents=True,exist_ok=True)
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'binder_choices':len(arithmetic),
                  'label_patterns':15,'complete_semantic_cases':total}))
