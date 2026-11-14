#!/usr/bin/env python3
"""Finite obstructions to two tempting restrictions of the propositional head.

This does not refute completeness of the full numerical calculus. It shows
that the restricted implicational head alone cannot replace the established
restricted-rho8 interface: K fails in a finite logical matrix with sound MP.
"""
from itertools import product
import json

def check(name, table, mode):
    values=range(3); designated=2; truth=2
    op=lambda a,b:table[a][b]
    assert op(truth,truth)==truth
    assert all(b==designated for b in values if op(designated,b)==designated)
    checked=[]
    for d,a,h in product(values,repeat=3):
        u=d if mode=='u_equals_D' else truth
        value=op(op(op(h,u),d),op(op(d,h),op(a,h)))
        assert value==designated
        checked.append([d,a,h,value])
    assert op(0,op(0,0))!=designated
    return dict(name=name,values=list(values),designated=[designated],
                truth=truth,implication=table,MP_sound=True,
                rho_cases=checked,K_counterexample=dict(a=0,b=0,
                    value=op(0,op(0,0))))

if __name__=='__main__':
    records=[
        check('Reflexive-only rho8',[[1,1,2],[1,2,2],[1,1,2]],'u_equals_D'),
        check('Truth-offset-only rho8',[[0,0,2],[2,2,2],[1,1,2]],'u_equals_truth'),
    ]
    print(json.dumps(dict(scope='The restricted propositional bases alone; not the full calculus',
                          records=records),indent=2))
