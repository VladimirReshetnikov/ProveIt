#!/usr/bin/env python3
"""Check exact decorated-tree complement identities and normalized half-truncation remainders.

Python 3.11+ standard library only; no network access.
"""
import argparse
from pathlib import Path
from fractions import Fraction as Q
from decimal import Decimal,localcontext
import json,math
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parents[1]/'results')
args=parser.parse_args()
P=args.output_dir.resolve()
P.mkdir(parents=True,exist_ok=True)
N=1001
fact=[math.factorial(i) for i in range(N+1)]
a=[1];d=[1]
for n in range(1,N+1):a.append(fact[n]+sum(a[i]*a[n-1-i] for i in range(n)))
for n in range(1,N+1):d.append(2*sum(a[i]*d[n-1-i] for i in range(n)))
def rem(n):return a[n]-sum(d[j]*fact[n-j] for j in range((n+1)//2))
def conv(a,b,n):
 out=[0]*(n+1)
 for i,x in enumerate(a):
  for j,y in enumerate(b[:n+1-i]):out[i+j]+=x*y
 return out
checks=[]
for n in range(2,65):
 B=n//2;f=fact[:B+1]+[0]*(n-B);ab=[1]
 for k in range(1,n+1):ab.append(f[k]+sum(ab[i]*ab[k-1-i] for i in range(k)))
 R=rem(n);assert R==ab[n] and R>0
 # Independently exact finite shape sectors.
 power=[1]+[0]*n;sectors=[]
 for s in range(n+1):
  power=conv(power,f,n)
  sectors.append(math.comb(2*s,s)//(s+1)*power[n-s])
 assert sum(sectors)==R
 main=fact[B]**2 if n%2 else 2*fact[B]*fact[B-1]
 assert sectors[1]==main
 checks.append({'n':n,'positive':True,'truncated_identity':True,'shape_identity':True})
coeffs=json.loads((P/'scalar-coefficients.json').read_text())
def dec(q):
 with localcontext() as ctx:
  ctx.prec=50
  return str(Decimal(q.numerator)/Decimal(q.denominator))
num=[]
for n in [40,41,100,101,200,201,400,401,1000,1001]:
 B=n//2;main=fact[B]**2 if n%2 else 2*fact[B]*fact[B-1]
 rat=Q(rem(n),main)
 cs=list(map(int,coeffs['odd' if n%2 else 'even']))
 row={'n':n,'ratio_to_exact_main':dec(rat),'errors':{}}
 for J in [0,1,2,3,6,9]:
  model=sum(Q(cs[j],B**j) for j in range(J+1))
  row['errors'][str(J)]=dec(rat-model)
 num.append(row)
out={'exact_checks':checks,'numerical_checks':num}
# ed. (2026-10-02): newline='\n' so the file is LF on Windows too (as delivered,
# the platform's line endings).
(P/'remainder-checks.json').write_text(json.dumps(out,indent=2)+'\n',newline='\n')

print("Wrote remainder-checks.json")
