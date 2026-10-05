"""Optional floating-point canonical product diagnostics; no certified gamma digits."""
import numpy as np, math,time
from scipy.linalg import eigh_tridiagonal
from scipy.special import ai_zeros
A=ai_zeros(1)[0][0]
v=np.array([1.]); logLambda=0.
for n in range(1,3001):
 k=np.arange(n+1,dtype=float)
 D=(2*n-2*k+1)/(n+k);D[0]=1
 b=(n-k[1:]+1)/np.sqrt((n+k[1:])*(n+k[1:]-1))
 vals,vec=eigh_tridiagonal(D,b,select='i',select_range=(n,n))
 lam=vals[0];phi=vec[:,0];phi*=np.sign(phi[0])
 R=np.ones(n) if n==1 else (n-k[:-1])/n*np.sqrt((n+k[:-1]-1)*(n+k[:-1])/(n*(n-1)))
 u=np.r_[v*R,0.]
 v=D*u;v[1:]+=b*u[:-1];v[:-1]+=b*u[1:];v/=lam
 logLambda+=math.log(lam)
 if n in [10,100,1000,3000]:
  cLam=math.exp(logLambda-n*math.log(4)-3*A*n**(1/3)-1.5*math.log(n))
  mass=np.dot(v,phi)
  gam=math.sqrt(2)*mass*cLam
  direct=math.exp(logLambda-n*math.log(4)-3*A*n**(1/3)-math.log(n))*v[0]
  print(n, 'mass', mass, 'C_lambda', cLam,'canonical_gamma_est',gam,'direct_gamma_est',direct,flush=True)
