#!/usr/bin/env python3
import hashlib,json,math,subprocess,sys
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];pkg=root/'research/current14-carrier64-pell-floor';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
# Independently expand X(2A−1)²−(X+1)²(2P), A=Y(X+1)+2, P=2XY²+1.
def add(a,b):
 c=defaultdict(int,a)
 for m,v in b.items():c[m]+=v
 return {m:v for m,v in c.items() if v}
def mul(a,b):
 c=defaultdict(int)
 for (i,j),u in a.items():
  for (k,l),v in b.items():c[i+k,j+l]+=u*v
 return {m:v for m,v in c.items() if v}
def neg(a):return {m:-v for m,v in a.items()}
x={(1,0):1};xp={(1,0):1,(0,0):1};a2m1={(1,1):2,(0,1):2,(0,0):3};p2={(1,2):4,(0,0):2}
assert add(mul(x,mul(a2m1,a2m1)),neg(mul(mul(xp,xp),p2)))=={(2,1):12,(1,1):12,(1,0):5,(2,0):-2,(0,0):-2}
def psi(p,n):
 a,b=0,1
 for _ in range(n):a,b=b,2*p*b-a
 return a
for N in range(13,21):
 R=2*N+1;X=1<<R;T=sum(math.comb(2*N,i)*X**(N-i) for i in range(N+1))//2;H=Fraction((X+1)**(2*N),2*X**N)
 assert 0<H-T<Fraction(1,4) and X>144*N
 for Y in (X**N//2+1,T,X**N-1):
  A=Y*(X+1)+2;P=2*X*Y*Y+1;c=psi(A,2*N+1);k=2*psi(P,N+1);r=Fraction(c,k)
  assert H<r<H+Fraction(1,4) and T<r<T+1 and c//k==T
for N in range(1,2001):
 z=math.comb(2*N,N)//2;assert (z&-z).bit_length()-1==N.bit_count()-1 and (2*N+1).bit_count()==N.bit_count()+1
for q in range(2,1000):
 assert (q*q-q-1)*(q*q-1)+(2*q+1)*(q-1)==q**4-q**3
 assert (4*q**3-1)-((4*q-2)*(q*q-1)+(2*q+1)*(q-1))==5*q-2
for f in ('current14-carrier64-sharp-growth-independent','current14-carrier64-bad-gap-exclusion-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=subprocess.run([sys.executable,'-I','-S','-B',str(pkg/'check.py')],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)==json.loads((pkg/'result.json').read_text()) and json.loads(r.stdout)['checker_sha256']==sha(pkg/'check.py')
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','scope':'conditional exact Pell floor, popcount and gap/rank bounds; inherited P72 theorem binding and actual port box; no new Lean proof or reverse equivalence'},indent=2))
