#!/usr/bin/env python3
"""Finite exact checks for the fixed-parameter power family; analytic proof separate."""
import sys
if not __debug__: raise SystemExit('Assertions must be enabled; do not use -O.')
from fractions import Fraction as F
from math import comb
from pathlib import Path
import argparse,json,hashlib
pa=argparse.ArgumentParser();pa.add_argument('--output-dir',default=str(Path(__file__).parent));ar=pa.parse_args();out=Path(ar.output_dir);out.mkdir(parents=True,exist_ok=True)
N=90;checks=0;mono=0;prefix={}
for alpha in (1,2,5):
 for beta in (0,1,2):
  a=[0]*(N+1);a[0]=1
  for k in range(1,N+1):
   cap=min(k**beta,N//k); factor=[comb(k**beta,j)*k**(alpha*j) for j in range(cap+1)]
   a=[sum(factor[j]*a[n-k*j] for j in range(min(cap,n//k)+1)) for n in range(N+1)]
  b=[0]*(N+1)
  for k in range(1,N+1):
   for j in range(1,N//k+1):b[k*j]+=(-1)**(j+1)*k**(beta+alpha*j+1)
  c=[0]*(N+1);c[0]=1
  for n in range(1,N+1):
   v=sum(b[j]*c[n-j] for j in range(1,n+1));assert v%n==0;c[n]=v//n
  assert a==c;checks+=N+1
  assert all(a[n+1]>a[n] for n in range(1,N));mono+=N-1
  prefix[f'{alpha},{beta}']=a[:12]
assert prefix['2,0']==[1,1,4,13,25,77,161,393,726,2010,3850,7874]
formal=0
for alpha in (F(1,3),F(1),F(2),F(7)):
 for d in range(1,6):
  for m in (2,5,11):
   for L in (2,3,9):
    # Integral of x^(d-1)*(alpha log x - t*x) to m, at t=alpha L/m.
    hard=alpha*m**d*(F(L,d)-F(1,d*d)-F(L,d+1))
    assert hard==alpha*m**d*(F(L,d*(d+1))-F(1,d*d))
    n=F(m**(d+1),d+1)
    hp=alpha*F(L-1,m);hpp=alpha/F(m*m);hppp=-2*alpha/F(m**3)
    assert -hpp/hp**3==-F(m)/(alpha**2*(L-1)**3)
    assert (3*hpp**2-hppp*hp)/hp**5==F(m)*(2*L+1)/(alpha**3*(L-1)**5)
    # Differentiate Q' = alpha(L-1)(m^(d-1)/(d+1)-n/m^2), n fixed.
    qp=alpha*(L-1)*(F(m**(d-1),d+1)-n/F(m*m))
    qpp=alpha/F(m)*(F(m**(d-1),d+1)-n/F(m*m))+alpha*(L-1)*(F((d-1)*m**(d-1),(d+1)*m)+2*n/F(m**3))
    assert qp==0;assert qpp==alpha*(L-1)*F(m)**(d-2)
    formal+=5
r={'status':'PASS','scope':'Supplementary finite identities, not the proof of the uniform analytic estimates.','coefficient_identities':checks,'strict_monotonicity_checks':mono,'parameter_identities':formal,'prefixes':prefix,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(out/'family_verification.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k!='prefixes'},indent=2))
