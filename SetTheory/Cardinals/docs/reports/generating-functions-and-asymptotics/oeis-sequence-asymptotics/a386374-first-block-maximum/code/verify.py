#!/usr/bin/env python3
"""Exact checks are proofs of finite identities only. Floating diagnostics are not certificates."""
import json, math, sys
from pathlib import Path
from fractions import Fraction as F
import mpmath as mp
BASE=Path(__file__).resolve().parent

def check(ok,label):
 if not ok: raise RuntimeError(label)

def bounded(n,m):
 b=[1]+[0]*n
 for t in range(1,n+1): b[t]=sum(math.comb(t,j)*b[t-j] for j in range(1,min(t,m)+1))
 return b

def exact(N):
 out=[1]+[0]*N
 for m in range(1,N+1):
  b=bounded(N-m,m)
  for n in range(m,N+1):out[n]+=math.comb(n,m)*b[n-m]
 return out

def comps(n):
 if not n:yield ()
 else:
  for j in range(1,n+1):
   for s in comps(n-j):yield (j,)+s

def strict_exact(N):
 out=[1]+[0]*N
 for m in range(1,N+1):
  b=bounded(N-m,m-1)
  for n in range(m,N+1):out[n]+=math.comb(n,m)*b[n-m]
 return out

def compcount(n):
 if not n:return 1
 return sum(math.factorial(n)//math.prod(math.factorial(s) for s in a) for a in comps(n) if a[0]==max(a))

def setcount(n):
 if n==0:return 1
 out=0
 def rec(sizes,left):
  nonlocal out
  if left==0:
   out+=sizes.count(max(sizes))*math.factorial(len(sizes)-1);return
  for j in range(len(sizes)):
   sizes[j]+=1;rec(sizes,left-1);sizes[j]-=1
  sizes.append(1);rec(sizes,left-1);sizes.pop()
 rec([1],n-1);return out

def truncated_exp(m,r):return sum(r**j/mp.factorial(j) for j in range(m+1)) if m>=0 else mp.mpf(0)
rho=mp.log(2)
def tail(m):
 t=rho**(m+1)/mp.factorial(m+1);s=t;j=m+1
 while abs(t)>abs(s)*mp.eps:
  j+=1;t*=rho/j;s+=t
 return s

def data(m):
 D=tail(m);a=truncated_exp(m-1,rho);b=truncated_exp(m-2,rho);c=truncated_exp(m-3,rho)
 d=D/a
 # The Taylor evaluation avoids subtracting nearly equal truncated exponentials.
 for _ in range(15):
  value=sum(truncated_exp(m-j,rho)*d**j/mp.factorial(j) for j in range(1,m+1))
  der=truncated_exp(m-1,rho+d)
  step=(value-D)/der;d-=step
  if abs(step)<abs(d)*mp.eps*10:break
 return D,a,b,c,d

def sums(n,M=100):
 pole=mp.mpf(0);approx=[mp.mpf(0) for _ in range(3)]
 for m in range(2,M+1):
  D,a,b,c,d=data(m);ell=mp.log1p(d/rho)
  cm=rho**(m-1)*mp.exp((m-1)*ell)/(mp.factorial(m)*truncated_exp(m-1,rho+d))
  pole+=cm*mp.exp(-n*ell)
  X=n*D;l2=-b/(2*rho*a**3)-1/(2*rho**2*a**2)
  l3=(3*b*b-a*c)/(6*rho*a**5)+b/(2*rho**2*a**4)+1/(3*rho**3*a**3)
  h1=(m-1)/(rho*a)-b/a**2;h2=(m-1)*l2-c/(2*a**3)+b*b/a**4
  q1=h1*X-l2*X*X;q2=h2*X*X-l3*X**3+q1*q1/2
  base=rho**(m-1)/(mp.factorial(m)*a)*mp.exp(-X/(rho*a))
  approx[0]+=base;approx[1]+=base*(1+q1/n);approx[2]+=base*(1+q1/n+q2/n**2)
 return pole,approx

def run():
 global rho
 mp.mp.dps=100;rho=mp.log(2)
 N=120;a=exact(N)
 expected=[1,1,3,10,47,276,2022,17606,179391,2093860,27581888,404680398,6541528886,115437202986,2206844818622,45408726154590,1000134868827263,23468606700087972,584340284516996400,15383829737201853518,426915367401366308112,12454073547413511363878]
 check(a[:len(expected)]==expected,'OEIS displayed terms')
 u=strict_exact(N)
 strict_expected=[1,1,1,4,17,96,652,5356,51361,568840,7157036,101048454,1582644956,27224336244,509883010652,10319902635984,224283040843745,5205554049801528,128430045368430484,3354764715348964222,92460461868234201532,2680680433302859375630,81542551486359310209666]
 check(u[:len(strict_expected)]==strict_expected,'strict OEIS displayed terms')
 for n in range(1,13):
  q=sum(math.factorial(n)//math.prod(math.factorial(t) for t in c) for c in comps(n) if len(c)==1 or c[0]>max(c[1:]))
  check(u[n]==q,'strict composition check '+str(n))
 for n in range(13):check(a[n]==compcount(n),'composition check '+str(n))
 for n in range(10):check(a[n]==setcount(n),'set partition check '+str(n))
 # Rational Taylor identities: general formal reversion and explicit Q1/Q2.
 import sympy as s
 z,r,A,B,C,m,X,v=s.symbols('z r A B C m X v',nonzero=True)
 d=z/A-B*z*z/(2*A**3)+(3*B*B-A*C)*z**3/(6*A**5)
 check(s.expand(A*d+B*d*d/2+C*d**3/6-z).series(z,0,4).removeO()==0,'reversion order 3')
 ell=s.log(1+d/r).series(z,0,4).removeO()
 h=((m-1)*s.log(1+d/r)-s.log((A+B*d+C*d*d/2)/A)).series(z,0,3).removeO()
 l2=-B/(2*r*A**3)-1/(2*r*r*A*A)
 l3=(3*B*B-A*C)/(6*r*A**5)+B/(2*r*r*A**4)+1/(3*r**3*A**3)
 h1=(m-1)/(r*A)-B/A**2;h2=(m-1)*l2-C/(2*A**3)+B**2/A**4
 for got,want,label in [(ell.coeff(z,2),l2,'ell2'),(ell.coeff(z,3),l3,'ell3'),(h.coeff(z,1),h1,'h1'),(h.coeff(z,2),h2,'h2')]:check(s.simplify(got-want)==0,label)
 U,V=s.symbols('U V')
 ex=s.exp(U*v+V*v*v).series(v,0,3).removeO()
 check(s.expand(ex.coeff(v,1)-U)==0,'Q1 exponential identity')
 check(s.expand(ex.coeff(v,2)-V-U*U/2)==0,'Q2 exponential identity')
 diag=[]
 for n in [20,40,80,120,1000,10000,1000000]:
  pole,ap=sums(mp.mpf(n),60)
  rec={'n':n,'relative_rootfree_errors':[mp.nstr(u/pole-1,15) for u in ap]}
  if n<=N:
   coeff=mp.mpf(a[n])/mp.factorial(n);rec['pole_abs_coefficient_error']=mp.nstr(coeff-pole/rho**n-1,15)
  diag.append(rec)
 phase=[]
 for m0 in [10,20,40,80]:
  for label,t in [('peak',mp.mpf(1)),('trough',mp.log(m0)+mp.log(mp.log(m0))-mp.log(rho))]:
   n=2*rho*t/tail(m0);pole,_=sums(n,m0+30);p=2*rho*pole
   phase.append({'m':m0,'type':label,'log10n':mp.nstr(mp.log10(n),12),'nP_over_m':mp.nstr(n*p/m0,15),'nP_over_logm':mp.nstr(n*p/mp.log(m0),15)})
 out={'exact_checks':{'oeis_terms':len(expected),'strict_oeis_terms':len(strict_expected),'strict_composition_n':12,'composition_n':12,'set_partition_n':9,'reversion_and_amplitude':'passed','assert_statements_used':False},'diagnostics_not_proof':diag,'phase_diagnostics_not_proof':phase}
 (BASE/('validation_optimized.json' if sys.flags.optimize else 'validation.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':run()
