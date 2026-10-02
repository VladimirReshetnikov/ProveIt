#!/usr/bin/env python3
"""Floating diagnostics only, not certified amplitude enclosures."""
import numpy as np
from scipy.special import ai_zeros
from pathlib import Path
import json
z=float(ai_zeros(1)[0][0]); output=[]
for d in (2,3,4):
 B=3*z*((d-1)/(d+1))**(2/3); eta=(d-1)**2/(2*(d+1)); rho=-eta-.5
 v=np.ones(1);samples=[]
 for N in range(1,12001):
  j=np.arange(1,N+1,dtype=float);p=np.ones(N)
  for h in range(1,d):p*=1-2*(j+h)/((d+1)*(N+j))
  w=np.zeros(N+1);w[1:]=p*v/2;w[:-2]+=v[1:]/2;v=w
  if N in (1000,2000,4000,8000,12000):
   n=N/2;logratio=np.log(v[0])-B*n**(1/3)-rho*np.log(n)
   row={'n':int(n),'raw_amplitude_ratio':float(np.exp(logratio))}
   if d==3:
    corr=B*B/162*n**(-1/3)+11*B/324*n**(-2/3)+(4*B**3/6561-3/16)/n
    row['corrected_through_n_inverse']=float(np.exp(logratio-corr))
   samples.append(row)
 output.append({'d':d,'samples':samples})
 print(d,samples,flush=True)
Path(__file__).with_name('numerical-diagnostics.json').write_text(json.dumps({'certified':False,'data':output},indent=2)+'\n')
