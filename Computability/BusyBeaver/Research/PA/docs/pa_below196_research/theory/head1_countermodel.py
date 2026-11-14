#!/usr/bin/env python3
"""Countermodel to replacing PA196's first head by its relative contrapositive.

Interpret implication classically, code 0 and code 1 as true, U as identity,
E as false, and M(a,b) as literal label equality. Every remaining PA196
axiom is designated, as is the replacement head. The old first head is not.
This algebraic model is of the numeric proof rules, not a standard FOL model.
"""
import functools
import itertools
import json
import math
from pathlib import Path

def pair(a,b):return (a+b)*(a+b+1)//2+b
def I(a,b):return 4*pair(a,b)
def M(a,b):return I(a,b)+1
def U(a,b):return 4*pair(b,a)+2
def E(a,b):return I(a,b)+3
def N(a):return I(a,1)
def And(a,b):return N(I(a,N(b)))
def Ex(a,b):return N(U(a,N(b)))

def decode(n):
    k=(math.isqrt(8*n+1)-1)//2
    b=n-k*(k+1)//2
    return k-b,b

@functools.lru_cache(None)
def value(n):
    if not n:return True
    a,b=decode(n//4)
    if n%4==0:return (not value(a)) or value(b)
    if n%4==1:return a==b
    if n%4==2:return value(a)
    return False

def old_head(d,h):return I(Ex(d,U(d,h)),h)
def replacement(d,h):return I(N(h),U(d,N(U(d,h))))
def heads(d,a,h):
    return [I(U(d,U(a,h)),U(a,U(d,h))),
            I(M(h,d),I(E(h,a),M(a,d))),
            I(E(h,d),I(M(a,h),M(a,d))),
            Ex(d,E(h,d)),
            I(U(d,a),I(U(d,I(a,h)),U(d,h)))]
def rho(a,b,c,u):return I(I(I(c,u),a),I(I(a,c),I(b,c)))
def gate(a,b,c):
    delta=I(E(a,b),U(c,E(a,b)))
    v=I(M(a,b),U(c,M(a,b)))
    p=I(c,M(c,b))
    s=U(b,And(I(M(a,b),p),I(M(c,b),c)))
    q=U(c,I(s,N(p)))
    return N(I(delta,I(v,q)))

def main():
    checks=0
    for d,a,h in itertools.product(range(12),repeat=3):
        assert value(replacement(d,h))
        assert all(value(x) for x in heads(d,a,h))
        assert value(gate(h,d,a))
        checks+=7
    for a,b,c,u in itertools.product(range(7),repeat=4):
        assert value(rho(a,b,c,u))
        checks+=1
    h=M(0,1)
    assert h==9 and not value(h)
    assert value(0) and value(1)
    assert value(replacement(0,h)) and not value(old_head(0,h))
    result={'old_head_witness':{'D':0,'H':h,'head_value':value(old_head(0,h))},
            'replacement_value':value(replacement(0,h)),
            'sample_formula_checks':checks,
            'all_parameter_argument':[
                'I is classical implication, so every rho8 and all pure propositional tautologies are true.',
                'U is identity, so GEN preserves truth; quantifier commutation and distribution are valid.',
                'E is always false, so both membership transport heads are valid.',
                'Code 1 is true, so N(A)=I(A,1) is true for every A.',
                'Therefore the equality-existence head, every guarded gate, and the replacement head are true.',
                'M(0,1) has value false, but the old first head with H=M(0,1) has the same false value.',
                'Induction on finite derivations proves that this old head cannot be derived from the changed calculus.'
            ],
            'conclusion':'The first-head replacement alone is not derivationally equivalent. Adding explicit 1 -> H repairs this specific defect, at an emitter cost.'}
    dest=Path(__file__).with_suffix('.json')
    dest.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
