# Interval arithmetic plus proved absolute Taylor-tail bounds.
# Runs producer first to reuse exact p coefficients, then encloses connection Wronskian.
import runpy
D=runpy.run_path(str(__file__).replace('certify_entringer.py','verify_entringer.py'))
from fractions import Fraction as Q
import mpmath as mp
from pathlib import Path
import json
mp.iv.dps=90; iv=mp.iv; M=D['M']; p=D['p'];rho=iv.pi/2
q=lambda x:iv.mpf(x.numerator)/x.denominator
h=[iv.mpf(0)]*(M+1)
for j in range(1,M,2):
 k=(j+1)//2;b=D['s'].bernoulli(2*k)
 h[j]=(-1)**k*2*q(Q(int(b.p),int(b.q)))*rho**(2*k)/D['math'].factorial(2*k)
f=[iv.mpf(0),iv.mpf(1)]
for k in range(M-1):
 f.append((((k+1)**2+2)*f[k+1]+sum((h[j]*f[k-j] for j in range(1,k+1)),iv.mpf(0)))/((k+2)*(k+1)))
z=rho/2;t=iv.mpf('0.5')
A=sum((q(x)*z**k for k,x in enumerate(p)),iv.mpf(0))
Ap=sum((k*q(x)*z**(k-1) for k,x in enumerate(p) if k),iv.mpf(0))
H=sum((x*t**k for k,x in enumerate(f)),iv.mpf(0))
Ht=sum((k*x*t**(k-1) for k,x in enumerate(f) if k),iv.mpf(0))
C=(A*Ht+rho*Ap*H)/2
# Absolute bounds: sum p_n*rho^n < 200; |f_n| <= (2/3)(3/2)^n.
# Consequently A<=200, rho|A'|<=200, |H|<=2, |Ht|<=16 at midpoint.
aerr=Q(200,2**(M+1));aperr=Q(200*(M+1),2**M)
herr=Q(8,3)*Q(3,4)**(M+1);hterr=Q(16,3)*(M+4)*Q(3,4)**(M+1)
# Include conservative product cross-terms, for any finite partial sums.
delta=(16*aerr+200*hterr+aerr*hterr+2*aperr+200*herr+aperr*herr)/2
if not delta<Q(1,10**44):
 raise RuntimeError('Analytic Taylor-tail certificate exceeds target width')
enclosed=C+iv.mpf([-1,1])*q(delta)
c=iv.pi*enclosed
result={'A0_interval':str(enclosed),'OEIS_c_interval':str(c),'analytic_tail_bound':str(delta),'analytic_tail_bound_upper':'1e-44','arithmetic':'mpmath interval arithmetic 90 decimal places; all exact rational inputs enclosed and pi is interval-valued','note':'Tail proof in proof_dossier.md. All polynomial recurrences and endpoint products are interval operations.'}
Path(__file__).with_name('entringer_connection_certificate.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
