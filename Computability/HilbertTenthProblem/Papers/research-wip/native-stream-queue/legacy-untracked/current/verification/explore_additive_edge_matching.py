#!/usr/bin/env python3
"""Exact bounded obstruction to replacing ordered edge matching by sums.

No claim about all nonlinear encodings or a complete system operation count.
"""
from pathlib import Path
from itertools import permutations
import json
import sympy as sp


def verify():
    edges=[(0,1),(1,2),(2,0)]
    cases=[]
    for word in permutations(range(3)):
        source=[edges[e][0] for e in word]
        target=[edges[e][1] for e in word]
        next_source=source[1:]+source[:1]
        energy=sum((a-b)**2 for a,b in zip(target,next_source))
        compatible=all(a==b for a,b in zip(target,next_source))
        assert (energy==0)==compatible
        # All scalar moments and indeed all per-edge features have the same
        # sum for every permutation. These first moments are explicit checks.
        moments=[sum(s**k for s in source)-sum(t**k for t in target) for k in range(1,7)]
        assert moments==[0]*6
        cases.append(dict(word=list(word),energy=energy,compatible=compatible,moment_differences=moments))
    assert sum(c['compatible'] for c in cases)==3
    bad=next(c for c in cases if c['word']==[0,2,1])
    assert bad['energy']==6 and not bad['compatible']
    M=sp.Matrix([[(dst-src)**2 for src,_ in edges] for _,dst in edges])
    # Every separable current/next cost has zero rectangular differences.
    rectangle=M[0,0]+M[1,1]-M[0,1]-M[1,0]
    assert rectangle==-2
    d1,d2,s1,s2=sp.symbols('d1 d2 s1 s2')
    general=(d1-s1)**2+(d2-s2)**2-(d1-s2)**2-(d2-s1)**2
    assert sp.expand(general+2*(d1-d2)*(s1-s2))==0
    # The remaining mixed term is a time-aligned product, not an ordinary
    # packed multiplication evaluated at one radix.
    product=sp.Poly((1+2*sp.Symbol('z'))*(2+sp.Symbol('z')),sp.Symbol('z'))
    assert product.nth(1)==5
    assert 1*2+2*1==4
    return dict(status='PASS_ADDITIVE_EDGE_MATCHING_OBSTRUCTION',
                deterministic_cycle_edges=edges,permutation_cases=cases,
                compatible_permutations=3,incompatible_permutations=3,
                scalar_moments_checked=6,false_order=[0,2,1],false_order_energy=6,
                squared_mismatch_matrix=[list(map(int,M.row(i))) for i in range(3)],
                nonzero_separability_rectangle=int(rectangle),
                general_mixed_difference='-2*(d1-d2)*(s1-s2)',
                ordinary_product_middle_coefficient=5,aligned_inner_product=4,
                scope='Every additive sum of per-edge features is permutation-invariant. Squared adjacent mismatch is not a separable current-edge plus next-edge cost. This excludes that direct replacement for the ordered route even on a deterministic three-cycle. It does not exclude nonlinear packed tests, finite-support masks, explicit neighboring-pair symbols or other history encodings; no complete operation count is claimed.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))
