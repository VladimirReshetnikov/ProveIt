"""Exact classification of affine Rule110 tests by two subset-sum weights.

This covers arbitrary real coefficients: each branch is solved as exact
linear conditions in the real weight ratio, including generic families.
It is not an optimality assertion about other arithmetic encodings.
"""
from itertools import product
from fractions import Fraction
from pathlib import Path
import json

S=[(0,0),(1,0),(0,1),(1,1)]
def add(x,y):return (x[0]+y[0],x[1]+y[1])
def sub(x,y):return (x[0]-y[0],x[1]-y[1])
def scale(k,x):return(k*x[0],k*x[1])
def val(x,r):return x[0]+x[1]*r
def possible(expr):
    out=set()
    for target in S:
        p,q=sub(expr,target)
        if p==q==0:return None
        if q:
            r=Fraction(-p,q)
            if r>=1:out.add(r)
    return out

ratios=set();generic=[];witnesses={};cases=0
for eps,s1,s2,s3,s4 in product(S,repeat=5):
    cases+=1
    a=sub(s4,eps);b=sub(s3,s1);c=sub(s3,s2)
    y=sub(add(s1,s2),add(s3,eps))
    candidates=None
    for actual in (sub(add(s4,s1),eps),sub(add(s4,s2),eps),
                   sub(add(s4,scale(2,s3)),add(s1,s2))):
        options=possible(actual)
        if options is not None:candidates=options if candidates is None else candidates&options
    if candidates==set():continue
    false=[]
    for av,bv,cv in product(range(2),repeat=3):
        yy=bv+cv-bv*cv*(av+1)
        false.append(add(eps,add(add(scale(av,a),scale(bv,b)),add(scale(cv,c),scale(1-yy,y)))))
    if candidates is None:
        if any(possible(f) is None for f in false):continue
        generic.append(dict(eps=eps,a=a,b=b,c=c,y=y))
    else:
        for r in candidates:
            allowed={val(z,r) for z in S}
            if any(val(z,r) in allowed for z in false):continue
            # Directly recheck all true and false assignments.
            for av,bv,cv in product(range(2),repeat=3):
                yy=bv+cv-bv*cv*(av+1)
                base=val(eps,r)+av*val(a,r)+bv*val(b,r)+cv*val(c,r)
                assert base+yy*val(y,r) in allowed
                assert base+(1-yy)*val(y,r) not in allowed
            ratios.add(r);witnesses[str(r)]=dict(eps=str(val(eps,r)),a=str(val(a,r)),b=str(val(b,r)),c=str(val(c,r)),y=str(val(y,r)))
result=dict(cases=cases,ratios=list(map(str,sorted(ratios))),generic=generic,witnesses=witnesses)
assert cases==1024 and ratios=={Fraction(3,2)} and generic==[]
result.update(status='AFFINE_TWO_WEIGHT_CLASSIFICATION_PASS',
              two_binary_digit_weights_possible=False,
              complete_parameter_domain='All positive real weights 0<s<=t and all real affine coefficients, normalized by s. No coefficient or ratio cutoff is used.',
              scope='Only a single affine projection of the four Boolean local variables into the two-weight subset-sum set is classified. Arbitrary alternative verifier architectures remain outside this result.',
              proof_note='../1980/EXPLORATION_RULE110_ONE_MASK_FIELD.md')
if __name__=='__main__':
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'],result['cases'],result['ratios'],'generic families:',len(generic))
