# Fixed-distance stabilization and inverse checks.
import sympy as s, mpmath as mp, json
from pathlib import Path
from contextlib import redirect_stdout
import io
with redirect_stdout(io.StringIO()): import verify as v
OUT=v.OUT; t=v.t; a=v.a; J=v.J
results=[]
for r in [0,1,2,3]:
 n0=max(2,4*r+1)
 rows=[v.stats(v.counts(n,r),n) for n in [n0,n0+1,n0+7]]
 alpha=[s.expand((n0+1)*rows[1][j]-n0*rows[0][j]) for j in range(4)]
 beta=[s.expand(n0*rows[0][j]-n0*alpha[j]) for j in range(4)]
 assert all(s.expand(alpha[j]+beta[j]/s.Integer(n0+7)-rows[2][j])==0 for j in range(4))
 sub={a[j]:alpha[j]+beta[j]*t*t for j in range(4)}
 absseries=s.series(s.exp(-beta[0]*t*t)*sum(v.d[j].subs(sub)*t**j for j in range(J+1)),t,0,J+1).removeO().expand()
 coeff=[absseries.coeff(t,j) for j in range(J+1)]
 logs=[s.Integer(0)]
 for j in range(1,J+1): logs.append(s.expand(coeff[j]-sum((k*logs[k]*coeff[j-k] for k in range(1,j)),s.Integer(0))/j))
 assert logs[1]==r+s.Rational(7,24)
 assert logs[2]==-s.Rational(r*(r+1),2)-s.Rational(7,48)
 assert logs[3]==r*r-s.Rational(r,8)+s.Rational(37,1920)
 gam=[mp.mpf(str(x)) for x in logs]
 def L(x):return x*(mp.log(x)-1)/2+mp.sqrt(x)-mp.log(2)/2-mp.mpf(1)/4-r+sum(gam[j]*x**(-mp.mpf(j)/2) for j in range(1,J+1))
 def D(x):return mp.log(x)/2+1/(2*mp.sqrt(x))-sum(mp.mpf(j)/2*gam[j]*x**(-mp.mpf(j)/2-1) for j in range(1,J+1))
 checks=[]
 for n in [100,250,499]:
  def count(n):return sum((-1)**k*x*v.I[n-2*k] for k,x in enumerate(v.counts(n,r)))
  exact=count(n); logy=mp.log(exact); x0=2*logy/mp.lambertw(2*logy/mp.e); x=x0
  for _ in range(4):x-=(L(x)-logy)/D(x)
  nextval=count(n+1); theta=mp.mpf('.37'); middlelog=(1-theta)*logy+theta*mp.log(nextval)
  chord=n+(middlelog-L(n))/(L(n+1)-L(n))
  checks.append({'n':n,'smooth_node_error':str(x-n),'chord_mid_error':str(chord-n-theta)})
 results.append({'r':r,'alpha':[str(x) for x in alpha],'beta':[str(x) for x in beta],'log_coefficients':[str(x) for x in logs[1:]],'inverse_checks':checks})
(OUT/'fixed-range-checks.json').write_text(json.dumps(results,indent=2));print(json.dumps(results,indent=2))
