#!/usr/bin/env python3
"""Complete exact rational inverse of the Keller map used in the article.

Examples:
    python3 code/rational_inverse.py 0 -4 2
    python3 code/rational_inverse.py 0 1 0
    python3 code/rational_inverse.py 4/27 4/3 1
Requires SymPy. Input coordinates are integers, fractions, or finite decimals.
"""
from __future__ import annotations
import argparse
import json
from fractions import Fraction
from math import lcm
import sympy as s


def parse_rational(text: str) -> s.Rational:
    try:
        value=Fraction(text)
    except (ValueError,ZeroDivisionError) as exc:
        raise argparse.ArgumentTypeError('Expected an integer, fraction, or finite decimal') from exc
    return s.Rational(value.numerator,value.denominator)


def F(x,y,z):
    u=1+x*y
    h=u*u*z+y*y*(1+3*u)
    return (u*h,y+3*x*h,x*(5-3*u-x*x*z))


def rational_preimages(A: s.Rational,B: s.Rational,C: s.Rational):
    """Return all distinct preimages over Q, with exact SymPy rational coordinates."""
    T=s.Symbol('T')
    g=s.Poly(C*T**3-2*T*T+B*T-2*A,T,domain=s.QQ)
    points=[]
    for root,multiplicity in g.ground_roots().items():
        if multiplicity != 1:
            continue
        w=g.diff().eval(root)/2
        assert w != 0
        points.append((1/w,root-w,5*w*w-3*root*w-C*w**3))
    if C==0:
        points.append((s.S.Zero,B,A-4*B*B))
    points=sorted(set(points),key=lambda v:tuple(v))
    for point in points:
        if any(s.cancel(x-y)!=0 for x,y in zip(F(*point),(A,B,C))):
            raise ArithmeticError('Internal reconstruction check failed')
    return points


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('A',type=parse_rational)
    parser.add_argument('B',type=parse_rational)
    parser.add_argument('C',type=parse_rational)
    args=parser.parse_args()
    points=rational_preimages(args.A,args.B,args.C)
    rows=[]
    for point in points:
        denominator=lcm(*(int(s.denom(v)) for v in point))
        rows.append({'point':[str(v) for v in point],
                     'common_denominator':denominator,
                     'integral':denominator==1})
    print(json.dumps({'target':[str(args.A),str(args.B),str(args.C)],
                      'rational_preimages':rows,
                      'rationally_soluble':bool(rows),
                      'integrally_soluble':any(r['integral'] for r in rows)},indent=2))

if __name__=='__main__':
    main()
