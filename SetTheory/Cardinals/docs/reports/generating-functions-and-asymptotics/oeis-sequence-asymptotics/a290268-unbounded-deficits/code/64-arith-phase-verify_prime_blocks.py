"""Exact arithmetic checks for the new prime-block reduction."""
from math import comb
from random import Random
from pathlib import Path
import json
import sympy as sp

def require(x,message):
 if not x:raise ArithmeticError(message)

def jet(d,k,q,modulus=None):
 r=2*d+q+1;c=2*d-q
 a=[1]+[0]*d
 for j in range(r):
  a=[(2*d-j)*a[i]+(a[i-1] if i else 0) for i in range(d+1)]
  if modulus:a=[x%modulus for x in a]
 if k==0:return a
 b=[c*a[i]+(2*a[i-1] if i else 0) for i in range(d+1)]
 if modulus:b=[x%modulus for x in b]
 for j in range(1,k):
  z=[c*b[i]+(2*b[i-1] if i else 0)+j*(j+r)*a[i] for i in range(d+1)]
  if modulus:z=[x%modulus for x in z]
  a,b=b,z
 return b

def valuation(n,p):
 require(n!=0,'zero has no finite valuation');n=abs(n);v=0
 while n%p==0:v+=1;n//=p
 return v

u,a,n=sp.symbols('u a n')
poly_checks=[]
for p in (3,5,7,11,13):
 prev,cur=sp.Integer(1),a
 for j in range(1,p):prev,cur=cur,sp.expand(a*cur+j*(j+n)*prev)
 require(sp.Poly(cur-a**p+a,a,n,modulus=p).is_zero,f'Q_p failed at {p}')
 poly_checks.append(p)

count=0;records=[]
for p in (3,5,7,11,13,17,19):
 for A in range(1,13):
  for B in range(min(12,((p-2)*A-1)//2)+1):
   d=A+B;k=(B+1)*p-1;q=(p-2)*A-2*B-1
   H=jet(d,k,q)[d]
   require(H%p!=0,f'prime-family failed {(p,A,B)}')
   residue=pow(2,B,p)*(-1)**(d+(2*d)%p+1)%p
   require(H%p==residue,f'explicit residue failed {(p,A,B)}')
   N=p*(A+2*B+2)-2
   cv=valuation(comb(N,k)*H,p)
   expect=1+valuation(d+1,p)+valuation(comb(d+B+1,B),p)
   require(cv==expect,f'coefficient valuation failed {(p,A,B)}')
   count+=1
   if p==3 and (A,B) in [(2,0),(4,1),(7,2)]:records.append({'prime':p,'A':A,'B':B,'d':d,'k':k,'q':q,'N':N,'H':H,'valuation':cv})

# Random complete polynomial-jet block identities, including higher terms.
rng=Random(20261001);random_checks=0
for rep in range(300):
 p=rng.choice((3,5,7,11));d=rng.randrange(1,20);k=rng.randrange(0,50);q=rng.randrange(0,80)
 r=2*d+q+1;A,s=divmod(r,p);B,t=divmod(k,p)
 small=[1]+[0]*d
 for j in range(s):small=[((2*d-j)*small[i]+(small[i-1] if i else 0))%p for i in range(d+1)]
 z0=[1]+[0]*d
 if t:
  z1=[(2*d-q)%p,2]+[0]*(d-1)
  for j in range(1,t):
   z2=[((2*d-q)*z1[i]+(2*z1[i-1] if i else 0)+j*(j+r)*z0[i])%p for i in range(d+1)];z0,z1=z1,z2
  z0=z1
 W=[sum(small[h]*z0[i-h] for h in range(i+1))%p for i in range(d+1)]
 C=A+B;expected=[0]*(d+1)
 for i in range(d+1):
  for j in range(C+1):
   degree=i+C+j*(p-1)
   if degree<=d:expected[degree]=(expected[degree]+pow(2,B,p)*(-1)**(C+j)*comb(C,j)*W[i])%p
 require(expected==jet(d,k,q,p),f'block identity failed {(p,d,k,q)}')
 random_checks+=1
out={'symbolic_prime_polynomials':poly_checks,'exact_family_and_valuation_cases':count,'random_full_jet_block_identities':random_checks,'examples':records,'status':'PASS'}
Path(__file__).with_name('prime_block_verification.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
