#!/usr/bin/env python3
"""Generate an exact member of the all-rank harmonic determinant family.

Example: python identity_cli.py --rank 3 --order 3 --shift 1
The displayed value is U + V*zeta(order, shift).  The weight is
Delta^(2*rank-2)(n+shift)^(-order)/(2*rank-2)!.
"""
from __future__ import annotations
import argparse,json,sys
from fractions import Fraction
from pathlib import Path
import sympy as sp
sys.path.insert(0,str(Path(__file__).resolve().parent/'verification'))
from core import uv,endpoint_matrix

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--rank',type=int,default=2)
 p.add_argument('--order',type=int,default=2)
 p.add_argument('--shift',default='1',help='A positive rational, e.g. 2/3')
 args=p.parse_args()
 if args.rank<2 or args.order<2:p.error('rank and order must both be at least 2')
 try:a=Fraction(args.shift)
 except (ValueError,ZeroDivisionError):p.error('shift must be a rational number')
 if a<=0:p.error('shift must be positive')
 aa=sp.Rational(a.numerator,a.denominator)
 U,V=uv(args.rank,aa,sp.Integer(args.order))
 E=endpoint_matrix(args.rank,aa,sp.Integer(args.order))
 print(json.dumps({'rank':args.rank,'order':args.order,'shift':str(aa),
      'finite_difference_order':2*args.rank-2,'U':str(U),'V':str(V),
      'value':'U + V*zeta(order, shift)','endpoint_matrix':[[str(x) for x in row] for row in E.tolist()],
      'normalization':'strictly ordered particle indices; no additional rank factorial',
      'proof':'Theorem 2.3 of the accompanying article'},indent=2))
if __name__=='__main__':main()
