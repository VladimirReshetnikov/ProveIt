"""High-precision diagnostics, not a directed interval certificate."""
import json,hashlib
from pathlib import Path
import mpmath as mp
mp.mp.dps=65
src=json.loads(Path(__file__).with_name('check_relative_numeric.json').read_text())
results=[]
for aa in (1,2,3):
 rows=[r for r in src['rows'] if r['a']==aa and (r['n']==1000 or (aa==3 and r['n'] in (100,3000)))]
 N=max(r['n'] for r in rows)
 # Independent logarithmic derivative recurrence, exact integer arithmetic.
 b=[0]*(N+1)
 for k in range(1,N+1):
  power=1
  for j in range(1,N//k+1):
   power*=k**aa
   b[k*j]+=k*power*(1 if j%2 else -1)
 coeff=[1]
 for n in range(1,N+1):
  z=sum(b[j]*coeff[n-j] for j in range(1,n+1))
  q,r=divmod(z,n)
  if r:raise ValueError('Nonintegral recurrence')
  coeff.append(q)
 a=mp.mpf(aa)
 roots=[mp.exp(1j*mp.pi*(2*j+1)/aa) for j in range(aa)]
 c0=mp.re(a*mp.log(2*mp.pi)/2+sum(-mp.loggamma(1-z)+z*(1-mp.log(-z)) for z in roots))
 if aa==1:c1=mp.mpf(7)/12-mp.euler
 elif aa==2:c1=mp.mpf(1)/12-mp.re(mp.digamma(1+1j))
 else:c1=mp.mpf(1)/12+mp.re(sum(z*z/a*mp.digamma(1-z) for z in roots))-mp.pi/a/mp.sin(2*mp.pi/a)
 for row in rows:
  n=row['n'];t=mp.mpf(row['t']);bb=-mp.lambertw(-t/a,-1).real;K=mp.exp(bb)
  # Logarithmic coordinate, independent of the original x-quadrature.
  def val(u,j):
   x=mp.exp(u);v=a*u-t*x;p=1/(1+mp.exp(-v))
   if j==0:return x*mp.log1p(mp.exp(v))
   if j==2:return x**3*p*(1-p)
   if j==3:return -x**4*p*(1-p)*(1-2*p)
   return x**5*p*(1-p)*(1-6*p*(1-p))
  cuts=[-mp.inf,0,bb/2,bb-1,bb,bb+1,bb+2,bb+4]
  # u>=bb+4 is smaller than exp(-a*b*exp(4)/2), far below the requested comparison.
  I,V,I3,I4=[mp.quad(lambda u:val(u,j),cuts) for j in (0,2,3,4)]
  base=mp.exp(I+n*t+c0)/mp.sqrt(2*mp.pi*V)
  correction=c1*t+I4/(8*V**2)-5*I3**2/(24*V**3)
  old=mp.mpf(row['uncorrected_relative_error']);new=base/coeff[n]-1
  err=abs(old-new)
  if err>mp.mpf('1e-25'):raise ValueError('Independent numerical disagreement: '+str(err))
  corrected=base*(1+correction)/coeff[n]-1
  if abs(corrected-mp.mpf(row['corrected_relative_error']))>mp.mpf('1e-25'):raise ValueError('Correction disagreement')
  results.append({'a':aa,'n':n,'exact_coefficient':str(coeff[n]),'uncorrected_relative_error':str(new),'corrected_relative_error':str(corrected),'agreement_absolute':str(err)})
  print(aa,n,mp.nstr(err,5),flush=True)
Path(__file__).with_suffix('.json').write_text(json.dumps({'directed_interval_certificate':False,'precision':65,'independent_exact_coefficient_method':'logarithmic derivative recurrence','independent_integration_variable':'log x','rows':results},indent=2)+'\n')
