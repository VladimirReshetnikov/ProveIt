#!/usr/bin/env python3
"""Numerical orientation checks only; the proof is analytic."""
import json
from pathlib import Path
import numpy as np
from scipy.linalg import eigvalsh_tridiagonal
from scipy.optimize import brentq

K=lambda t: np.sin(t)/t-2*np.cos(t)-2
F=lambda t: (2*t*t-1)*np.sin(t)+t*np.cos(t)
t0=brentq(K,2.7,2.9)
tc=brentq(F,2.9,3.1)
kc=K(tc)
rows=[]
for d in [500,2000,8000]:
  for kap in [0.005,0.015,0.025]:
    k=round(kap*d); kap=k/d
    t=brentq(lambda t: K(t)-kap,t0,tc)
    y=1/t**2
    J=np.arcsin((kap+2)/np.sqrt(y+4))-np.arcsin(2/np.sqrt(y+4))
    for b in [-8,0,9]:
      R=4*d+b+1
      ii=np.arange(1,k,dtype=float)
      eig=eigvalsh_tridiagonal(np.zeros(k),np.sqrt(ii*(ii+R)))
      alpha=(eig[eig>1e-10]**2)/4
      rho=d*d*y
      m=min(2*d,2*d+b)
      j=np.arange(1,m+1,dtype=float)
      mu=np.sum(rho/(rho+j*j))+np.sum(alpha/(rho-alpha))
      V=np.sum(rho*j*j/(rho+j*j)**2)-np.sum(alpha*rho/(rho-alpha)**2)
      targetV=F(t)/(4*t*(np.cos(t)+2*t*np.sin(t)))
      resolvent=np.sum(1/(2*np.sqrt(rho)-eig))
      shift=np.prod(1-b/(2j*np.sqrt(rho)-1j*eig))
      rows.append(dict(d=d,k=k,b=b,kappa=kap,mean_error=mu/d-(1-kap)/2,
                       curvature_error=V/d-targetV,
                       resolvent_error=resolvent-J/2,
                       shift_error=abs(shift-np.exp(1j*b*J/2))))
output={'status':'Numerical orientation only; not a proof or finite-depth certificate',
        't0':t0,'tc':tc,'kappa_c':kc,'rows':rows}
path=Path(__file__).with_name('spectral_numeric.json')
path.write_text(json.dumps(output,indent=2)+'\n')
for d in [500,2000,8000]:
  r=[x for x in rows if x['d']==d]
  print(d, {key:max(abs(x[key]) for x in r) for key in
      ['mean_error','curvature_error','resolvent_error','shift_error']})
