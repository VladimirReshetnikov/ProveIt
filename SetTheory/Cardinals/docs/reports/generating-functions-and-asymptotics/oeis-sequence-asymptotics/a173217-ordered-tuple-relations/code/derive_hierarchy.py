#!/usr/bin/env python3
"""Exact symbolic fourth-order hierarchy; finite coefficient construction only."""
import argparse
from validation import integer, require, load_pinned_json, write_json
import sympy as s,json
from pathlib import Path
ROOT = Path(__file__).resolve().parent
n,t,u,w,L,z,h=s.symbols('n t u w L z h')

def trunc_exp(poly,R):
 integer("R", R)
 out=s.Integer(1); power=s.Integer(1)
 for k in range(1,R+1):
  power=s.series(power*poly,t,0,R+1).removeO().expand()
  out+=power/s.factorial(k)
 return s.series(out,t,0,R+1).removeO().expand()

def data(d,R):
 integer("d", d, 2)
 integer("R", R)
 ep=0; dp=0
 for q in range(1,R+2):
  S=s.summation(h**q,(h,0,n-1))
  ep+=(-1)**(q-1)*u**q/s.Integer(q)*t**(2*q)*S.subs(n,1/t)
 for q in range(1,R+1):
  S=s.summation(h**q,(h,0,d*L-1))
  dp+=t**q*S/(q*d**q)
 ep=s.series(ep-u/2,t,0,R+1).removeO().expand()
 E=trunc_exp(ep,R)
 D=trunc_exp(dp,R)
 def theta(P): return s.expand(w*s.diff(P,w)+w*P/2)
 def oper(Q,P):
  out=0; cur=P
  for q in range(s.degree(Q,L)+1):
   out+=Q.coeff(L,q)*cur
   cur=theta(cur)
  return s.expand(out)
 C=[]
 for r in range(R+1):
  C.append(s.factor(sum(oper(D.coeff(t,b).expand(),E.coeff(t,r-b).subs(u,w)) for b in range(r+1))))
 return C
REFERENCE_DIGEST = "b48f6fda72cf2193531f4e9039c00fc9a6025ae27d43ad3d4550692986a5ae72"

def derive():
 out={}
 for d in [2,3,4]:
  C=data(d,4)
  if d==2:
   coeff=[s.factor(c.subs(w,-z*z/4)) for c in C]
  else:
   master=sum(t**r*c.subs(w,-z**d/d**d*t**(d-2)) for r,c in enumerate(C))*s.exp(-z**d/(2*d**d)*t**(d-2))
   master=s.series(master,t,0,5).removeO().expand()
   coeff=[s.factor(master.coeff(t,r)) for r in range(5)]
  out[str(d)]=list(map(str,coeff))
 return out

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument("--output", type=Path, default=ROOT/"hierarchy_coefficients.json")
 parser.add_argument("--reference", type=Path, default=ROOT/"hierarchy_reference.json")
 args=parser.parse_args()
 expected=load_pinned_json(args.reference,REFERENCE_DIGEST,"Hierarchy reference")
 out=derive()
 require(out==expected,"Derived hierarchy does not match reference coefficients")
 write_json(args.output,out)
 print('{"coefficient_count":15,"status":"PASS"}')

if __name__=="__main__":
 main()
