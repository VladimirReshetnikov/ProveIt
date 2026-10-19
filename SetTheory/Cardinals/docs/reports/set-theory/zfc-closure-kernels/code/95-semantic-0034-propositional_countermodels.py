#!/usr/bin/env python3
"""Replay a fresh finite-matrix obstruction to L[u:=F] + K.

This is an obstruction for the pure propositional basis. It does not
interpret the retained quantified/equality schemas and hence makes no
claim about the full enriched calculus.
"""
from itertools import product
import json
from pathlib import Path

def main():
    table=((2,2,2),(2,0,2),(0,0,2))
    F,top=0,2
    def I(a,b):return table[a][b]
    def L(a,b,c):return I(I(I(c,F),a),I(I(a,c),I(b,c)))
    def K(a,b):return I(a,I(b,a))
    def S(a,b,c):return I(I(a,I(b,c)),I(I(a,b),I(a,c)))
    valid=dict(L_fixed_F=all(L(*v)==top for v in product(range(3),repeat=3)),
               K=all(K(*v)==top for v in product(range(3),repeat=2)),
               EFQ=all(I(F,a)==top for a in range(3)),
               DNE=all(I(I(I(a,F),F),a)==top for a in range(3)),
               MP=all(not(a==top and I(a,b)==top) or b==top for a,b in product(range(3),repeat=2)))
    assert all(valid.values())
    failures=dict(identity=[a for a in range(3) if I(a,a)!=top],
                  S=[v for v in product(range(3),repeat=3) if S(*v)!=top])
    assert failures['identity'] and failures['S']
    result=dict(status='PASS_PURE_PROPOSITIONAL_OBSTRUCTION',matrix=table,bottom=F,designated=[top],
                valid=valid,refutations=failures,
                scope='No interpretation of retained quantifier/equality axioms is supplied')
    (Path(__file__).resolve().parent/'propositional_countermodels_check.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
