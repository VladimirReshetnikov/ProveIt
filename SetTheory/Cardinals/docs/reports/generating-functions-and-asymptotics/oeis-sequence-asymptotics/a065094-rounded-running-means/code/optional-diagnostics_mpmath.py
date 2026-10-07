#!/usr/bin/env python3
"""Optional 120-digit mpmath diagnostics. These are NOT interval proofs."""
from fractions import Fraction as F
from pathlib import Path
import sys,json
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).absolute().parent.parent/'code'))
from certify_amplitudes import compute
from formal_series import PUBLISHED_C as c
def floating_checks():
 import mpmath as mp
 mp.mp.dps=120
 cert=compute(N=20000,digits=110)
 out=[]
 for mode in ['floor','ceiling']:
  A=sum(mp.mpf(v) for v in cert['sequences'][mode]['A'])/2
  a=total=1;wanted=[25,100,400,1600,6400]
  for n in range(1,max(wanted)+1):
   if n in wanted:
    x=mp.mpf(n);p=mp.laguerre(n-1,0,-1)
    lead=A*mp.exp(2*mp.sqrt(x)-mp.mpf('0.5'))/(2*mp.sqrt(mp.pi)*x**mp.mpf('.25'))
    aprox=lead*sum(mp.mpf(v.numerator)/v.denominator/x**(mp.mpf(j)/2) for j,v in enumerate(c))
    D=A*mp.exp(-mp.mpf('.5'))/mp.sqrt(2*mp.pi)
    t=-mp.lambertw(-2*D*D/mp.mpf(a)**2,-1)/2
    inv=t*t/4+mp.mpf(17)/48+1/(48*t)-mp.mpf(539)/(2880*t*t)-mp.mpf(51)/(640*t**3)-mp.mpf(25517)/(241920*t**4)
    out.append({'mode':mode,'n':n,'shadow_residual':mp.nstr(mp.mpf(a)-A*p,25),'relative_allorder_error':mp.nstr(aprox/a-1,25),'inverse_error':mp.nstr(inv-n,25)})
   a+=(total+(n-1 if mode=='ceiling' else 0))//n;total+=a
 return {'scope':'120-digit floating diagnostics, not interval proof','rows':out}

if __name__=="__main__": print(json.dumps(floating_checks(),indent=2,sort_keys=True))
