#!/usr/bin/env python3
"""Finite evidence for the square/native code isomorphism.
The unbounded argument is in square_pair_conjugacy.md. No TM state claim.
"""
from pathlib import Path
from functools import cache
from math import isqrt
import sys,json,itertools
if not __debug__:raise RuntimeError('Run without -O.')
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'architectures'))
import pattern_oracle as O
C,P,T=O.load_source()

def cantor(a,b):return (a+b)*(a+b+1)//2+b

def cantor_inv(q):
    m=(isqrt(8*q+1)-1)//2;b=q-m*(m+1)//2
    return m-b,b

def square(a,b):return a*a+a+b if a>=b else b*b+a

def square_inv(q):
    m=isqrt(q);d=q-m*m
    return (d,m) if d<m else (m,d-m)

@cache
def f(n):
    if n==0:return 0
    a,b=square_inv(n//4)
    assert a<n and b<n
    return 4*cantor(f(a),f(b))+n%4

@cache
def g(n):
    if n==0:return 0
    a,b=cantor_inv(n//4)
    assert a<n and b<n
    return 4*square(g(a),g(b))+n%4

# Interned normalized hereditary terms represent denotations without evaluating
# gigantic expanded numerical bundle codes. Keys are structural, no collisions.
def b(tag,left,right):
    return ('z',) if tag==0 and left==right==('z',) else (tag,left,right)

@cache
def square_tree(n):
    if n==0:return ('z',)
    a,c=square_inv(n//4)
    return b(n%4,square_tree(a),square_tree(c))

@cache
def native_tree(n):
    if n==0:return ('z',)
    a,c=cantor_inv(n//4)
    return b(n%4,native_tree(a),native_tree(c))

def evaluate_template(t,args):
    values=list(args)+[('z',)]
    for tag,l,r in t.steps:values.append(b(tag,values[l],values[r]))
    return values[t.root]

def tests():
    count={'inverse_pair_cases':0,'inverse_code_cases':0,'constructor_equations':0,
           'all_template_assignments':0,'gate_equivalences':0,'generated_prefix_denotations':0}
    for n in range(16384):
        assert square(*square_inv(n))==n
        assert cantor(*cantor_inv(n))==n
        assert g(f(n))==n and f(g(n))==n
        assert square_tree(n)==native_tree(f(n))
        count['inverse_pair_cases']+=2;count['inverse_code_cases']+=2
    for a,bv in itertools.product(range(64),repeat=2):
        assert square_inv(square(a,bv))==(a,bv)
        assert square(a,bv)>=a+bv
        for tag in range(4):
            assert f(4*square(a,bv)+tag)==4*cantor(f(a),f(bv))+tag
            assert g(4*cantor(a,bv)+tag)==4*square(g(a),g(bv))+tag
            count['constructor_equations']+=2
    for rule,t in T.items():
        for args in itertools.product((0,1,4,8),repeat=t.arity):
            # This is an exact finite symbolic-code equality, including every
            # occurrence of c as label or matrix in the full bundle.
            left=evaluate_template(t,[square_tree(a) for a in args])
            right=evaluate_template(t,[native_tree(f(a)) for a in args])
            assert left==right
            count['all_template_assignments']+=1
    for a,bv,c in itertools.product(range(32),repeat=3):
        assert (c!=a and c!=bv)==(f(c)!=f(a) and f(c)!=f(bv))
        count['gate_equivalences']+=1
    import canonical_arena as A
    nodes=A.generated_prefix(4095);vals=A.native_values(nodes)
    assert vals==[f(i) for i in range(len(nodes))]
    count['generated_prefix_denotations']=len(nodes)
    assert f(0)==0 and f(1)==1 and f(4)==8 and f(8)==4
    assert f(1+3)!=f(1)+f(3)
    return dict(count,all_passed=True,scope='Finite exact arithmetic and symbolic template diagnostics; ordinary unbounded proof is square_pair_conjugacy.md; no binary machine claim.')
if __name__=='__main__':
    result=tests();(HERE/'square_pair_conjugacy_results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
