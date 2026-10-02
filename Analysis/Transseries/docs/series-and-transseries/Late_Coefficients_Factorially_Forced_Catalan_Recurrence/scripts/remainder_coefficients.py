#!/usr/bin/env python3
"""Compute exact scalar coefficients of factorial-basis half-truncation remainders.

Python 3.11+ standard library only; no network access.
"""
import argparse
import json,math
from fractions import Fraction as Q
from pathlib import Path
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parents[1]/'results')
args=parser.parse_args()
P=args.output_dir.resolve()
P.mkdir(parents=True,exist_ok=True)
J=9
# Truncated polynomials in x=1/B.
def mul(a,b,L):
 c=[Q(0)]*(L+1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):
   if i+j<=L:c[i+j]+=x*y
 return c

def inverse_falling(k,L):
 p=[Q(0)]*k+[Q(1)]
 p=(p+[Q(0)]*(L+1))[:L+1]
 for i in range(k):p=mul(p,[Q(i)**r for r in range(L+1)],L)
 return p
f=[math.factorial(n) for n in range(J+3)];a=[1];d=[1]
for n in range(1,J+3):a.append(f[n]+sum(a[i]*a[n-1-i] for i in range(n)))
for n in range(1,J+3):d.append(2*sum(a[i]*d[n-1-i] for i in range(n)))
b=[0]+[sum(d[i]*d[j]*d[t-1-i-j] for i in range(t) for j in range(t-i)) for t in range(1,J+3)]
even=[Q(0)]*(J+2);odd=[Q(0)]*(J+2)
for t in range(1,J+2):
 for u in range(t+1):
  z=mul(inverse_falling(u,J+1),inverse_falling(t-u,J+1),J+1)
  for k in range(1,J+2):even[k-1]+=b[t]*z[k]/2
 for u in range(t):
  z=mul(inverse_falling(u,J+1),inverse_falling(t-1-u,J+1),J+1)
  for k in range(J+1):odd[k]+=b[t]*z[k]
x={'b':b[1:],'even':[str(z) for z in even[:J+1]],'odd':[str(z) for z in odd[:J+1]]}
# ed. (2026-10-02): newline='\n' so the file is LF on Windows too (as delivered,
# the platform's line endings).
(P/'scalar-coefficients.json').write_text(json.dumps(x,indent=2)+'\n',newline='\n')

print("Wrote scalar-coefficients.json")
