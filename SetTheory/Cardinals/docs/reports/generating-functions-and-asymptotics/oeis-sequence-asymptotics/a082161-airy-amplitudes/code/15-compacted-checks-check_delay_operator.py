from pathlib import Path
"""Exact gauge identity and numerical global/ground delay-operator checks."""
from fractions import Fraction
from math import factorial
import json
import numpy as np
from scipy.linalg import eigh_tridiagonal
for N in range(6,61):
 for j in range(1,N-1):
  lhs=Fraction(factorial(N-2)*factorial(N-3),factorial(N-j-1)*factorial(N+j-4))/Fraction(factorial(N+1)*factorial(N),factorial(N-j+1)*factorial(N+j))
  rhs=Fraction((N-j+1)*(N-j)*(N+j)*(N+j-1)*(N+j-2)*(N+j-3),(N+1)*N*N*(N-1)*(N-1)*(N-2))
  assert lhs==rhs,(N,j)
def ground(N,vector=True):
 j=np.arange(1,N+2,dtype=float); b=np.sqrt((N-j+2)/(N+j))
 vals,vecs=eigh_tridiagonal(np.zeros(N+2),b,select='i',select_range=(N+1,N+1))
 v=vecs[:,0];v*=np.sign(v[0]);v[np.arange(len(v))%2!=N%2]=0;v*=np.sqrt(2)
 return vals[0],v
out=[]
for N in [100,200,500,1000,2000,5000,10000]:
 lam,g=ground(N);l1,_=ground(N-1);l2,_=ground(N-2);_,old=ground(N-3)
 j=np.arange(1,N-1,dtype=float)
 rat2=(N-j+1)*(N-j)*(N+j)*(N+j-1)*(N+j-2)*(N+j-3)/((N+1)*float(N)**2*(N-1)**2*(N-2))
 ell=2*(N-j-2)/((N+j)*(N+j-2))*np.sqrt(rat2)
 factor=(N/(N-3))**.25/(lam*l1*l2)
 B=np.zeros(N+2);B[1:N-1]=factor*ell*old[:N-2]
 diff=np.linalg.norm(B-g/(4*N)); scalar=np.dot(g,B)
 out.append({'N':N,'N_times_delay_norm':float(N*max(ell)),'scaled_ground_residual':float(N**(4/3)*diff),'N_times_ground_projection':float(N*scalar)})
 print(out[-1],flush=True)
open(Path(__file__).with_name('delay-operator-check.json'),'w').write(json.dumps({'exact_identity':'all integer points 6<=N<=60, 1<=j<=N-2 passed rational equality','numeric_is_not_proof':True,'samples':out},indent=2))
