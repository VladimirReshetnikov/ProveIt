#!/usr/bin/env python3
"""Symbolic all-fixed-order de-Poissonization of exact lattice clusters.
Requires SymPy 1.14.0; every displayed coefficient is exact.
"""
import json,sympy as s
from pathlib import Path

x,t,m,ell,theta=s.symbols('x t m ell theta')

def exponential_coeffs(h,M):
 E=[s.Integer(1)]
 for r in range(1,M+1):E.append(s.expand(sum(j*h[j]*E[r-j] for j in range(1,r+1))/r))
 return E

def falling_operators(M):
 h=[s.Integer(0)]+[-s.summation(ell**r,(ell,0,m-1))/r for r in range(1,M+1)]
 return exponential_coeffs(h,M)

def derive(rows,M,vary=False):
 q=theta if vary else s.Integer(1)
 b=[[s.Rational(v) for v in row] for row in rows]
 a=b[2][0]
 h=[s.Integer(0)]*(M+1)
 for j in range(2,M+3):
  for off in range(3):
   r=j-2+off
   if 1<=r<=M:h[r]+=b[j][off]*(q*t)**j
 H=exponential_coeffs(h,M)
 P=falling_operators(M)
 def apply(p,f):
  pol=s.Poly(p,m); powers=[f]
  for j in range(pol.degree()):powers.append(s.expand(t*s.diff(powers[-1],t)+2*a*q*q*t*t*powers[-1]))
  return sum(c*powers[k[0]] for k,c in pol.terms())
 out=[]
 for r in range(M+1):
  out.append(s.factor(sum(apply(P[k],H[r-k])/q**k for k in range(r+1)).subs(t,1)))
 return out

if __name__=='__main__':
 rows=json.loads(Path('cluster_coefficients.json').read_text());out={}
 for piece,data in rows.items():
  M=len(data['b_j_coefficients_n2_n_1'])-3
  c=derive(data['b_j_coefficients_n2_n_1'],M)
  out[piece]=[str(z) for z in c]
  print(piece,out[piece])
  # uniform density coefficient functions through second order
  print('density',piece,[str(z) for z in derive(data['b_j_coefficients_n2_n_1'],min(M,2),True)])
 Path('asymptotic_coefficients.json').write_text(json.dumps(out,indent=2)+'\n')
