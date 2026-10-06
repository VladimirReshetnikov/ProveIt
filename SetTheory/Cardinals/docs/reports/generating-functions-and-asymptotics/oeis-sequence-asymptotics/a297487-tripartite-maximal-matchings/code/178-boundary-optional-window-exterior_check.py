#!/usr/bin/env python3
import mpmath as mp,json
from pathlib import Path
mp.mp.dps=70
import argparse
p=argparse.ArgumentParser(description='Optional exterior diagnostics; not interval certificates')
p.add_argument('--output-dir',required=True,type=Path)
output=p.parse_args().output_dir
output.mkdir(exist_ok=False)
out=[]
for n in [100,1000,10000,100000]:
 for c in [mp.mpf('.5'),mp.mpf(1),mp.mpf(2)]:
  d=int(c*n)+1;cn=mp.mpf(d)/n;lam=cn**-2
  t=mp.mpf(1);Z=t;terms=[t]
  for j in range(n):
   t*=mp.mpf(n-j)**2/((d+2*j+1)*(d+2*j+2)*(j+1));Z+=t;terms.append(t)
   if t<mp.mpf('1e-60'):
    rr=mp.mpf(n-j-1)**2/((d+2*j+3)*(d+2*j+4)*(j+2)) if j+1<n else 0
    tail=t*rr/(1-rr);break
  f=lam**2+(2*lam**2+3*lam)/cn
  tv=mp.mpf(0);p=mp.exp(-lam)
  for j,t in enumerate(terms):
   if j:p*=lam/j
   tv+=abs(t/Z-p)/2
  r=dict(n=n,d=d,cn=str(cn),first_correction=str(-f),scaled_relative_error=str(n*(Z/mp.exp(lam)-1)),tv_to_exact_poisson=str(tv),tail_upper=str(tail))
  out.append(r);print(n,d,'target',mp.nstr(-f,15),'residual',mp.nstr(n*(Z/mp.exp(lam)-1),15),'TV',mp.nstr(tv,8))
(output/'exterior_diagnostics.json').write_text(json.dumps(out,indent=2)+'\n')
