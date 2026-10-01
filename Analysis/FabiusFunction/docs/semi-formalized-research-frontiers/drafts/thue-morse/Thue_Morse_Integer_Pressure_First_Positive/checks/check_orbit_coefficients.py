"""Compare exact finite-matrix second coefficients to finite inverse-tree sums."""
from pathlib import Path
import json
import sympy as s
import mpmath as mp
mp.mp.dps=70
rows=[]
for m in range(2,7):
 I=list(range(1-m,m));d=len(I)
 def a(j):return s.Rational(s.binomial(2*m,m+j),4**m) if -m<=j<=m else s.S.Zero
 V=s.Matrix(d,d,lambda k,r:2*a(2*I[k]-I[r]))
 B1=s.Matrix(d,d,lambda k,r:-2*(2*I[k]-I[r])*V[k,r])
 B2=s.Matrix(d,d,lambda k,r:(m-2*(2*I[k]-I[r])**2)*V[k,r])
 f=s.zeros(d,1);f[m-1]=1;u=s.zeros(d,1);v=s.zeros(d,1)
 ev=s.Matrix(1,d,[(-1)**abs(r) for r in I])
 for N in range(1,13):
  f,u,v=V*f,V*u+B1*f,V*v-B1*u+B2*f
  assert sum(u)==0 and sum(v)==0
  if N not in [1,2,4,7,12]:continue
  exact=(ev*v)[0]
  if N<=7:
   total=mp.mpf(0)
   for q in range(-2**(N-1),2**(N-1)):
    w=mp.mpf(q)+mp.mpf('.5')
    tans=[mp.tan(mp.pi*w/2**j)for j in range(1,N+1)]
    S=sum(tans);T=sum(t*t for t in tans)
    total+=(2**N*mp.sin(mp.pi*w/2**N))**(-2*m)*(2*m*m*S*S-m*T)
   err=abs(total-mp.mpf(str(exact.p))/int(exact.q))
   assert err<mp.mpf('1e-60')
  else:err=None
  rows.append(dict(m=m,N=N,exact=str(exact),decimal=str(s.N(exact,16)),finite_orbit_error=None if err is None else str(err)))
(Path(__file__).resolve().parent.parent/'data'/'finite_orbit_checks.json').write_text(json.dumps({'rows':rows,'all_finite_orbit_checks_below_1e_minus_60':True},indent=2)+'\n')
print('Verified 20 finite inverse-tree identities at 70-digit precision against exact rational matrices; recorded five N=12 convergence checks.')
