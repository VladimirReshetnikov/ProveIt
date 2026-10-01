"""Exact fourth eigenfunction response and second post-cancellation pressure coefficient."""
from pathlib import Path
import sympy as s,json
ROOT=Path(__file__).resolve().parents[1]/"data"

def c(k):return (-1)**(k+1)*2**(2*k)*s.bernoulli(2*k)/s.factorial(2*k)
def R(k):return (2**(2*k)-1)*c(k)

def responses(m,N=4):
 I=list(range(1-m,m));d=len(I)
 def a(j):return s.Rational(s.binomial(2*m,m+j),4**m) if -m<=j<=m else s.S.Zero
 V=s.Matrix(d,d,lambda k,r:2*a(2*I[k]-I[r]));Ms=[]
 for n in range(N+1):
  M=s.zeros(d)
  for k in range(d):
   for r in range(d):
    j=2*I[k]-I[r]
    if not -m<=j<=m:continue
    M[k,r]=V[k,r]*sum((-1)**h*s.binomial(m+j,h)*s.binomial(m-j,n-h)for h in range(n+1))
  Ms.append(M)
 A=s.eye(d)-V;C=A.copy();C[0,:]=s.ones(1,d);inv=C.inv()
 y=s.zeros(d,1);y[0]=1;h=[inv*y];lam=[s.S.One]
 for n in range(1,N+1):
  rhs=sum((Ms[j]*h[n-j]for j in range(1,n+1)),s.zeros(d,1));ln=sum(rhs);lam.append(ln)
  rhs-=sum((lam[j]*h[n-j]for j in range(1,n+1)),s.zeros(d,1));assert sum(rhs)==0
  original_rhs=rhs.copy();rhs[0]=0;v=inv*rhs;assert A*v==original_rhs and sum(v)==0;h.append(v)
 ev=s.Matrix(1,d,[(-1)**abs(r)for r in I])
 B=-(ev*h[2])[0];D=(ev*h[4])[0]
 E=D+s.Rational(2*m+2,3)*B+s.Rational(m*(10*m+7),45)*R(m)-s.Rational(m,m+2)*R(m+2)
 if m==2:E-=R(2)**2/2
 return B,D,s.factor(E)
prev={v['m']:s.Rational(v['pressure_even_coefficients'][str(2*v['m']+4)])for v in json.loads((ROOT/'higher_pressure_exploration.json').read_text())['rows']}
rows=[]
for m in range(2,13):
 B,D,E=responses(m)
 assert D>0 and E>0
 if m in prev:assert E==prev[m]
 rows.append({'m':m,'B':str(B),'D':str(D),'next_pressure_coefficient':str(E)})
 print(m,D,E,flush=True)
# Exact start of the uniform bound and simple monotonicity certificate.
q=4**6*s.binomial(12,4)-s.Rational(120**4,24)*s.Rational(2,3)**6
assert q>0
assert s.Rational(7,6)**4*s.Rational(4,9)<1
out={'rows':rows,'m6_positive_bracket':str(q),'tail_ratio_upper_bound_for_m_ge6':str(s.Rational(7,6)**4*s.Rational(4,9)),'independent_pressure_comparison_m2_to_8':True,'all_checks_passed':True}
(ROOT/'fourth_response_checks.json').write_text(json.dumps(out,indent=2)+'\n')
