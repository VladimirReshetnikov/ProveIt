#!/usr/bin/env python3
"""Finite algebra certificate for the arbitrary-term fourth-field obstruction.

This checks the finite premises of the accompanying unbounded theorem.
It does not claim that enumerating finite terms proves the theorem: the
closure induction in formalism_results.tex is the universal step.
"""
from itertools import product
from pathlib import Path
import argparse, json

M = ((3,3,3,3),(3,3,1,3),(3,3,3,3),(0,0,0,3))
VALUES = range(4)
D = 3
F = 0
S = frozenset((0,1,3))

def imp(a,b): return M[a][b]
def luk(a,b,c,u): return imp(imp(imp(c,u),a),imp(imp(a,c),imp(b,c)))
def neg(a): return imp(a,F)
def conj(a,b): return neg(imp(a,neg(b)))
def forall(xs): return D if all(x == D for x in xs) else F

def main():
    if not __debug__:
        raise SystemExit('Run with assertions enabled; omit -O and -OO.')
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path)
    args=ap.parse_args()
    failures=[(a,b,c,u,luk(a,b,c,u)) for a,b,c,u in product(VALUES,repeat=4) if luk(a,b,c,u)!=D]
    assert failures==[(0,3,1,2,0),(1,3,1,2,0)]
    assert all(imp(a,b) in S for a,b in product(S,repeat=2))
    assert all(a in S for a in (F,D))
    assert all(neg(a) in (F,D) for a in VALUES)
    assert all(conj(a,b) in (F,D) for a,b in product(VALUES,repeat=2))
    assert all(imp(a,b) in (F,D) and ((imp(a,b)==D)==(a!=D or b==D))
               for a in VALUES for b in (F,D))
    assert all(neg(a)==(F if a==D else D) for a in VALUES)
    assert all(conj(a,b)==(D if a==b==D else F) for a,b in product(VALUES,repeat=2))
    assert imp(1,2)!=D
    assert all(imp(D,b)!=D or b==D for b in VALUES)
    assert all(imp(a,a)==D and imp(F,a)==D for a in VALUES)
    assert all(imp(a,imp(b,a))==D for a,b in product(VALUES,repeat=2))
    restricted=0
    for a,b,c in product(VALUES,repeat=3):
        generated={F,D,a,b,c}
        while True:
            closed=generated|{imp(x,y) for x,y in product(generated,repeat=2)}
            if closed==generated:break
            generated=closed
        assert all(luk(a,b,c,u)==D for u in generated),(a,b,c,generated)
        restricted+=len(generated)
    distribution=0
    for n in (1,2,3):
        for aa,bb in product(product(VALUES,repeat=n),repeat=2):
            assert imp(forall([imp(a,b)for a,b in zip(aa,bb)]),imp(forall(aa),forall(bb)))==D
            distribution+=1
    result={
      'status':'FINITE_PREMISES_PASS',
      'matrix':[list(r)for r in M], 'designated':D,'falsum':F,
      'all_unrestricted_rho8_valuations':256,
      'exact_unrestricted_failures':[list(x)for x in failures],
      'closed_subalgebra':sorted(S),
      'subalgebra_implication_pairs':len(S)**2,
      'generated_subalgebra_restricted_rho8_checks':restricted,
      'distribution_vector_checks_lengths_1_2_3':distribution,
      'theorem_scope':'Every finite fourth-field term built from the first three fields and constants by implication, with arbitrary Boolean-valued extra leaves/operators, preserves the HC countermodel.',
      'unbounded_step':'Structural induction on arbitrary finite terms and the self-contained HC soundness proof in formalism_results.tex.'}
    raw=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.out:args.out.write_text(raw)
    print(raw,end='')

if __name__=='__main__':main()
