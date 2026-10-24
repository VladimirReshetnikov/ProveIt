"""Finite independent audit of the generalized full-residue construction.
Only modular matrices and integer identities are used; no producer is imported.
These finite examples do not substitute for the universal proof.
"""
from pathlib import Path
import json,math
R=Path(__file__).resolve().parent

def mul(a,b,m=None):
 c=(a[0]*b[0]+a[1]*b[2],a[0]*b[1]+a[1]*b[3],a[2]*b[0]+a[3]*b[2],a[2]*b[1]+a[3]*b[3])
 return tuple(v%m for v in c) if m else c

def matrix_power(a,n,m=None):
 q=(1,0,0,1)
 while n:
  if n&1:q=mul(q,a,m)
  a=mul(a,a,m);n//=2
 return q

def uv(a,n):
 q=matrix_power((a,-1,1,0),n)
 return q[2],q[0]+q[3]

examples=[];classes=0
for A,B,N in [(4,1,1),(4,1,2),(4,1,3),(6,1,1),(6,1,5),(8,1,3),(4,3,1)]:
 C,d=uv(A,B);D=d*d;modulus=4*N*C*C*d
 step=(A%modulus,-1%modulus,1,0);q=(1,0,0,1);n=0
 while True:
  q=mul(q,step,modulus);n+=1
  if q==(1,0,0,1):break
  if n>100000:raise RuntimeError('finite period budget exceeded')
 un,vn=uv(A,n)
 if un%modulus:raise RuntimeError('period does not give divisibility')
 xi=un//(4*C*C*d);r=vn//2
 E0=C*C*xi;E=D*E0;E2=E0*E
 F=4*(A*A-4)*E2+1;G=(A//2-1)*(F-1)-1;Omega=16*E
 if F!=r*r or Omega!=4*d*un:raise RuntimeError('saturation reconstruction')
 lam=4*n*r;periodpart=lam//math.gcd(lam,Omega)
 if math.gcd(periodpart,xi)!=1:raise RuntimeError('period prime absorption')
 if matrix_power((A,-1,1,0),lam,F)!=(1,0,0,1):raise RuntimeError('period modulo F')
 for c in [0,1,2,5,xi-1]:
  # L is positive, divisible byperiodpart, and in the requestedxi-class.
  L=periodpart*((c*pow(periodpart,-1,xi))%xi+xi)
  if L%xi!=c%xi or L%periodpart or (Omega*L)%lam:raise RuntimeError('CRT class')
  j=B+Omega*L
  # The exact H0 is astronomical. Its residue moduloOmega*F*xi
  # suffices to check integrality and the recovered y class.
  mm=Omega*F*xi
  H0=matrix_power((2*G,-1,1,0),j,mm)[2]
  numerator=(H0-C-(B-C)*F)%mm
  if numerator%(Omega*F):raise RuntimeError('interpolated quotient is nonintegral')
  ymod=numerator//(Omega*F)
  if ymod%xi!=c%xi:raise RuntimeError('interpolated residue class')
  classes+=1
 examples.append({'A':A,'B':B,'N':N,'matrix_period_n':n,'xi_bits':xi.bit_length(),'index_j_bits':j.bit_length()})
receipt={'status':'PASS','examples':examples,'residue_classes':classes,'scope':'Finite modular construction audit; universal interpolation proved in PROOF.md.'}
(R/'INTERPOLATION_CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
