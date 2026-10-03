#!/usr/bin/env python3
"""Exact application checks; these are examples, not a general matrix front end."""
from pathlib import Path
import json
from profiles import ExpPoly, make_chain, build_profiles, verify_profiles, first_negative


def mm(a, b):
    return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]


def main():
    stats = {}
    # Nonlinear triangular register update and its invariant monomial lift.
    lift = [[1,0,0,0],[0,2,0,0],[0,0,4,0],[0,0,1,1]]
    checked = 0
    for u in range(-3,4):
        for v in range(-2,3):
            x,y = u,v
            for n in range(21):
                assert x == (2**n)*u
                assert 3*(y-v) == u*u*(4**n-1)
                mon = [[1],[x],[x*x],[y]]
                xn,yn = 2*x,y+x*x
                assert mm(lift,mon) == [[1],[xn],[xn*xn],[yn]]
                assert 3*y-20*x+65 == u*u*4**n-20*u*2**n+3*v-u*u+65
                x,y = xn,yn
                checked += 1
    stats['triangular_state_and_lift_checks'] = checked
    # Exact global minimum in the manuscript example.
    f = ExpPoly({1:[96],2:[-20],4:[1]})  # original sequence minus (-32)
    chain,_ = make_chain(f,{1:0,2:0,4:0})
    charts = build_profiles(chain,None)
    assert verify_profiles(chain,charts,None)
    assert first_negative(charts[0]) is None
    zero_runs = [r for r in charts[0] if r.sign == 0]
    assert len(zero_runs) == 1 and zero_runs[0].lo == zero_runs[0].hi == 3
    stats['global_minimum_example'] = {'minimum':-32,'least_minimizer':3}
    # Integer matrices with individually split positive spectrum but bad product.
    U = [[2,1],[0,1]]
    V = [[1,0],[-1,2]]
    P = mm(U,V)
    assert P == [[1,2],[-1,2]]
    tr = P[0][0]+P[1][1]
    det = P[0][0]*P[1][1]-P[0][1]*P[1][0]
    assert (tr,det,tr*tr-4*det) == (3,4,-7)
    stats['nonclosure_product'] = {'matrix':P,'trace':tr,'determinant':det,'discriminant':-7}
    # Negative rational roots: two positive-base residue sequences.
    # f(n)=(-2)^n + n*(-1)^n - 5, split n=2m+r.
    residue_terms = [{4:[1],1:[-5,2]}, {4:[-2],1:[-6,-2]}]
    for r, terms in enumerate(residue_terms):
        g = ExpPoly(terms)
        chain,_ = make_chain(g,{4:0,1:1})
        profile = build_profiles(chain,None)
        assert verify_profiles(chain,profile,None)
        for m in range(41):
            n = 2*m+r
            assert g.value(m) == (-2)**n+n*((-1)**n)-5
    stats['parity_identity_checks'] = 82
    path = Path(__file__).resolve().parent.parent/'data'/'application_checks.json'
    path.write_text(json.dumps(stats,indent=2)+'\n')
    print(json.dumps(stats,indent=2))


if __name__ == '__main__':
    main()
