"""Exact exploratory pressure jets from Fourier eigenvalue recursion."""
import sympy as s
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[1]/"data"

def jet(m,N):
 I=list(range(1-m,m));d=len(I)
 def a(j):return s.Rational(s.binomial(2*m,m+j),4**m) if -m<=j<=m else s.S.Zero
 V=s.Matrix(d,d,lambda k,r:2*a(2*I[k]-I[r]))
 M=[s.Matrix(d,d,lambda k,r:V[k,r]*s.Rational((-2*(2*I[k]-I[r]))**n,s.factorial(n)))for n in range(N+1)]
 A=s.eye(d)-V;C=A.copy();C[0,:]=s.ones(1,d);inv=C.inv()
 rhs=s.zeros(d,1);rhs[0]=1;h=[inv*rhs];L=[s.S.One]
 for n in range(1,N+1):
  rhs=sum((M[j]*h[n-j]for j in range(1,n+1)),s.zeros(d,1))
  lam=sum(rhs);L.append(lam)
  rhs-=sum((L[j]*h[n-j]for j in range(1,n+1)),s.zeros(d,1))
  assert sum(rhs)==0
  rhs[0]=0;hn=inv*rhs
  assert sum(hn)==0
  h.append(hn)
 realL=[x*((-1)**(n//2)) if n%2==0 else s.S.Zero for n,x in enumerate(L)]
 assert all(L[n]==0 for n in range(1,N+1,2))
 p=[s.S.Zero]
 for n in range(1,N+1):p.append(s.factor(realL[n]-sum(k*p[k]*realL[n-k]for k in range(1,n))/n))
 assert p[2*m]==0
 return p

rows=[]
for m in range(2,9):
 p=jet(m,2*m+8)
 rec={'m':m,'pressure_even_coefficients':{str(n):str(p[n])for n in range(2,len(p),2)},'post_cancellation_signs':[s.sign(p[n]) for n in range(2*m+2,len(p),2)]}
 rec['post_cancellation_signs']=list(map(int,rec['post_cancellation_signs']))
 rows.append(rec)
 print(m,[(n,str(p[n]),int(s.sign(p[n])))for n in range(2*m+2,len(p),2)],flush=True)
(ROOT/'higher_pressure_exploration.json').write_text(json.dumps({'status':'Exploratory exact finite computations; no universal assertion','rows':rows},indent=2)+'\n')
