#!/usr/bin/env python3
"""Finite Boolean obstruction to an identity translation of the dual-B trial.

This is not an inequiconsistency proof.  It only disproves derivability of the
old B scheme, and explosion, in the proposed replacement theory under this
truth-preserving interpretation of its listed rules and schemes.
"""
import argparse
from itertools import product
import json
from pathlib import Path


def imp(a, b): return (not a) or b
def membership(a, b): return a == 0 and b == 0
def equality(a, b): return False
def universal(d, a): return True
def neg(a): return imp(a, True)  # code1=M(0,0), hence true in this model
def exists(d, a): return neg(universal(d, neg(a)))
def conjunction(a, b): return neg(imp(a, neg(b)))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    bits = (False, True)
    counts = {}
    def check(name, values):
        values = list(values)
        assert all(values), name
        counts[name] = len(values)
    check('rho', (imp(imp(imp(h,u),d), imp(imp(d,h),imp(a,h)))
                  for h,u,d,a in product(bits, repeat=4)))
    check('h2', (imp(universal(0,universal(1,h)), universal(1,universal(0,h)))
                 for h in bits))
    check('h3', (imp(m1,imp(False,m2)) for m1,m2 in product(bits, repeat=2)))
    check('h4', (imp(False,imp(m1,m2)) for m1,m2 in product(bits, repeat=2)))
    check('h5', [exists(0,equality(0,1))])
    check('h6', (imp(universal(0,a), imp(universal(0,imp(a,h)),universal(0,h)))
                 for a,h in product(bits, repeat=2)))
    check('diagonal', (imp(h,universal(0,h)) for h in bits))
    check('dual_B', (imp(h,universal(0,exists(0,h))) for h in bits))
    gates=[]
    for m1,m2,c in product(bits, repeat=3):
        V=imp(m1,universal(0,m1)); P=imp(c,m2)
        S=universal(0,conjunction(imp(m1,P),imp(m2,c)))
        Q=universal(0,imp(S,neg(P)))
        gates.append(neg(imp(V,Q)))
    check('gate', gates)
    check('modus_ponens_preserves_truth',
          ((not(a and imp(a,b))) or b for a,b in product(bits, repeat=2)))
    check('generalization_preserves_truth',
          ((not h) or universal(0,h) for h in bits))
    H=membership(1,1)
    old_B=imp(exists(0,universal(0,H)), H)
    explosion=imp(membership(0,0), H)
    assert H is False and old_B is False and explosion is False
    assert imp(True,True) is True  # code0=I(0,0) is consistently interpreted.
    result={
      'status':'PASS', 'scheme_truth_cases':counts,
      'model':{'implication':'material implication','code0':True,
               'M(a,b)':'true exactly when a=b=0','E(a,b)':False,
               'U(d,A)':True,'code1=M(0,0)':True},
      'witness':{'H':'M(1,1)','H_code':17,'old_B(0,H)':old_B,
                 'code1_implies_H':explosion},
      'scope':'No identity/theorem-preserving derivation of old B or explosion from the stated dual-B replacement. This does not exclude an alternate refutation compiler or an equiconsistency theorem.'}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
