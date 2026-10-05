import mpmath as mp,json
from pathlib import Path
mp.mp.dps=35
out=[]
for aa in (1,2,3):
 maxn=3000; coeff=[1]+[0]*maxn
 for k in range(1,maxn+1):
  for n in range(maxn,k-1,-1):coeff[n]+=k**aa*coeff[n-k]
 a=mp.mpf(aa)
 if aa==1:c0=mp.log(2*mp.pi)/2-1;c1=mp.mpf(7)/12-mp.euler
 elif aa==2:c0=mp.log1p(-mp.exp(-2*mp.pi));c1=mp.mpf(1)/12-mp.re(mp.digamma(1+1j))
 else:
  c0=a*mp.log(2*mp.pi)/2+mp.nsum(lambda k:mp.log1p(k**(-a)),[1,mp.inf])-mp.pi/mp.sin(mp.pi/a)
  c1=mp.mpf(1)/12+mp.nsum(lambda k:k/(1+k**a),[1,mp.inf])-mp.pi/a/mp.sin(2*mp.pi/a)
 def moments(t,which):
  b=-mp.lambertw(-t/a,-1).real;K=mp.exp(b)
  def fun(x):
   y=x**a*mp.exp(-t*x);p=y/(1+y)
   if which==0:return mp.log1p(y)
   if which==1:return x*p
   if which==2:return x*x*p*(1-p)
   if which==3:return -x**3*p*(1-p)*(1-2*p)
   return x**4*p*(1-p)*(1-6*p*(1-p))
  return mp.quad(fun,[0,1,K/2,K,K+K/b,2*K,mp.inf])
 for n in (100,1000,3000):
  K0=mp.sqrt(2*n);guess=a*mp.log(K0)/K0
  t=mp.findroot(lambda t:moments(t,1)-n,(guess*mp.mpf('.9'),guess*mp.mpf('1.1')))
  I,V,I3,I4=[moments(t,j) for j in (0,2,3,4)]
  base=mp.exp(I+n*t+c0)/mp.sqrt(2*mp.pi*V)
  correction=c1*t+I4/(8*V**2)-5*I3**2/(24*V**3)
  vals={'a':aa,'n':n,'t':str(t),'uncorrected_relative_error':str(base/coeff[n]-1),'corrected_relative_error':str(base*(1+correction)/coeff[n]-1),'correction':str(correction)}
  print(vals,flush=True);out.append(vals)
Path(__file__).with_suffix('.json').write_text(json.dumps({'precision':35,'rigorous':False,'rows':out},indent=2)+'\n')
