#!/usr/bin/env python3
"""Independent finite part of the outer-head rho8 obstruction.

No imports from predecessor packets. The HC realization and ZFC soundness
argument are mathematical and are explained in outer_head_obstruction.md.
"""
from itertools import product
from pathlib import Path
import json

M=((3,3,3,3),(3,3,1,3),(3,3,3,3),(0,0,0,3))
V=range(4)
I=lambda a,b:M[a][b]
L=lambda a,b,c,u:I(I(I(c,u),a),I(I(a,c),I(b,c)))
Q=lambda xs:3 if all(x==3 for x in xs) else 0
E=lambda a,b:3 if a==b else 0

def main():
    bad=[(a,b,c,u,L(a,b,c,u)) for a,b,c,u in product(V,repeat=4) if L(a,b,c,u)!=3]
    assert bad==[(0,3,1,2,0),(1,3,1,2,0)]
    allowed=(0,1,3)
    checks=[L(a,b,c,u)==3 for a,b,c in product(V,repeat=3) for u in allowed]
    assert len(checks)==192 and all(checks)
    irange=sorted({I(a,b) for a,b in product(V,repeat=2)})
    erange=sorted({E(a,b) for a,b in product(V,repeat=2)})
    qrange=sorted({Q(xs) for n in (1,2,3) for xs in product(V,repeat=n)})
    assert irange==[0,1,3] and erange==qrange==[0,3]
    # Strict field bound used in the independent specialization theorem.
    def pair(a,b):return (a+b)*(a+b+1)//2+b
    for a,b in product(range(80),repeat=2):
        for tag in range(4):
            n=4*pair(a,b)+tag
            if n>=2:assert max(a,b)<=n-2
    result={'status':'FINITE_OUTER_HEAD_OBSTRUCTION_PASS','matrix':M,
            'all_unrestricted_rho8_failures':bad,
            'uniform_allowed_fourth_values':allowed,'uniform_cases':192,
            'implication_range':irange,'quantifier_range':qrange,'equality_range':erange,
            'theorem_scope':'All implication-, quantifier-, or equality-headed fourth inputs, and any simultaneous family thereof, in the inherited full HC model.',
            'limits':'The program checks the finite matrix and a bounded sample of the arithmetic bound; the unbounded HC/model and bound arguments are supplied in prose.'}
    path=Path(__file__).with_name('outer_head_obstruction.json')
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
