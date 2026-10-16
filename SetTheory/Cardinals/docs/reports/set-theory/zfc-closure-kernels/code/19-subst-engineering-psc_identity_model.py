#!/usr/bin/env python3
"""A small executable regression for the complete raw-PSC algebraic model.

This independently simplifies the finite-sort obstruction supplied in the
latest research archive: all quantifiers act as identity; Rel(i,j) is true
exactly when i>=2 and j=0. This is a model of the *coded proof calculus*,
not a one-domain first-order membership structure.
"""
from __future__ import annotations
import argparse, hashlib, itertools, json, math, sys
from functools import cache
from pathlib import Path

def member(i,j): return i>=2 and j==0

def unpair(n):
    s=(math.isqrt(8*n+1)-1)//2
    b=n-s*(s+1)//2
    return s-b,b

@cache
def code_value(n,base):
    if n==0:return True
    q,tag=divmod(n,base)
    if base==4 and tag==1:return False
    a,b=unpair(q)
    if tag==0:return not code_value(a,base) or code_value(b,base)
    if tag==(1 if base==3 else 2):return member(a,b)
    return code_value(b,base) # every All operator is identity

def evaluate(f,nums,values):
    if f==0:return True
    if f==1:return False
    if isinstance(f,str):return values[f]
    kind,a,b=f
    if kind=='imp':return not evaluate(a,nums,values) or evaluate(b,nums,values)
    if kind=='all':return evaluate(b,nums,values)
    if kind=='rel':return member(nums.get(a,a),nums.get(b,b))
    raise ValueError(kind)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args()
    research=args.repo.resolve()/'Computability/BusyBeaver/Research/ZFC'
    sys.path.insert(0,str(research))
    import theory_backend_experiment as t
    import psc_backend_experiment as psc
    spec,specsha=t.published_spec()
    rows=spec['ax_rows']('a','h','b','c','u')
    forms=[rows[i] for i in (1,3,5,7)]
    vr=t.Imp(t.Rel('a','b'),t.All('c',t.Rel('a','b')))
    checks=0
    for bits in itertools.product((False,True),repeat=5):
        values=dict(zip(('a','h','b','c','u'),bits))
        for f in forms:
            assert evaluate(f,{'a':0,'b':1,'c':2,'u':3},values)
            checks+=1
    pscform=psc.psc_template()
    # Remove the conclusion's leading All(1,...) and wrap the whole formula
    # in an existential: each suggested cheap repair remains true here.
    free_root=t.Imp(pscform[1],pscform[2][2])
    prefixed=t.Ex(2,pscform)
    ir=t.All(1,t.Not(t.Rel(1,1)))
    ui=t.Imp(t.All('a','b'),'b')
    numeric_cases=0
    for base in (3,4):
        assert code_value(0,base) and not code_value(1,base)
        for c in range(10000):
            nums={'a':c%5,'b':(c//5)%5,'c':c,'k':c+2}
            values={'a':code_value(nums['a'],base),'b':code_value(nums['b'],base),
                    'c':code_value(c,base)}
            for f in (pscform,free_root,prefixed,ir,ui,vr):
                assert evaluate(f,nums,values)
            numeric_cases+=1
    matrix_cases=0
    for k,v in itertools.product(range(2,130),(False,True)):
        nums={'k':k};values={'c':v}
        assert evaluate(pscform,nums,values)
        matrix_cases+=1
    # This is a valid ordinary FO substitution instance, rejected by the model.
    separating=t.Imp(t.All(2,t.Rel(2,0)),t.Rel(1,0))
    assert not evaluate(separating,{}, {})
    data={'source_pin':'47f3a3602946dfe48803a91a910c646e74637ac8',
          'quantifiers':'identity','membership':'i >= 2 and j == 0',
          'logical_boolean_cases':checks,'numeric_PSC_codes_checked':numeric_cases,
          'independent_matrix_bit_cases':matrix_cases,
          'all_PSC_instances_general_argument':'For k>=2, SB=true, guard=false, support=true.',
          'same_variable_specialization_survives':True,
          'remove_root_forall_survives':True,'existential_prefix_survives':True,
          'irreflexivity_survives':True,
          'cross_variable_specialization_rejected':'All(2,Rel(2,0)) -> Rel(1,0)',
          'ordinary_FOL_model':False,
          'prior_stronger_scope':'Latest supplied finite-sort model already obstructs both C/G and PSC.',
          'exact_psc_source_sha256':hashlib.sha256(Path(psc.__file__).read_bytes()).hexdigest(),
          'spec_sha256':specsha,
          'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    args.output.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
    print(json.dumps(data,indent=2,sort_keys=True))

if __name__=='__main__':main()
