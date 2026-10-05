"""Floating-point diagnostics only; not a certified numerical amplitude."""
import numpy as np, math
from scipy.linalg import eigh_tridiagonal
from scipy.special import ai_zeros,gammaln
A=ai_zeros(1)[0][0]
C={}
for n in range(7):
 for m in range(n+1):
  C[n,m]=1 if m==0 else (m+1)*C.get((n-1,m),0)+C[n,m-1]-(m-1)*C.get((n-2,m-1),0)
def R(n,k):
 if n==1:return np.ones_like(k)
 return (n-k)/n*np.sqrt((n+k-1)*(n+k)/(n*(n-1)))
vs=[np.array([1.])];ks=[1.];logG=0.
for n in range(1,3001):
 k=np.arange(n+1,dtype=float)
 D=(2*n-2*k+1)/(n+k);D[0]=1
 b=(n-k[1:]+1)/np.sqrt((n+k[1:])*(n+k[1:]-1))
 vals,vec=eigh_tridiagonal(D,b,select='i',select_range=(n,n))
 lam=vals[0];kap=lam-1/n;phi=vec[:,0];phi*=np.sign(phi[0]);logG+=math.log(kap);ks.append(kap)
 if n<=3:
  logs=gammaln(n+1)-gammaln(n-k+1)+.5*(gammaln(n)+gammaln(n+1)-gammaln(n+k)-gammaln(n+k+1))
  v=np.array([C[n+j,n-j]*math.exp(-gammaln(n+j+1)-logG-logs[j]) for j in range(n+1)])
 else:
  x=np.r_[R(n,k[:-1])*vs[-1],0.]
  v=D*x;v[1:]+=b*x[:-1];v[:-1]+=b*x[1:];v/=kap
  kd=k[:n-1]
  diag=(2*n-2*kd-3)/((n+kd)*(n+kd-1));diag[0]=(n-2)/(n*(n-1))
  diag*=R(n,kd)*R(n-1,kd)
  kl=k[1:n]
  low=(n-kl-1)*(2*n-2*kl+1)/((n+kl)*(n+kl-1)*(n+kl-2))
  low*=R(n,kl-1)*R(n-1,kl-1)/b[:n-1]
  den=kap*ks[-2]
  v[:n-1]-=diag*vs[-2]/den;v[1:n]-=low*vs[-2]/den
  kl=k[1:n-1]
  low=(n-kl-1)*(n-kl-2)/((n+kl)*(n+kl-1)*(n+kl-2)*(n+kl-3))
  low*=R(n,kl-1)*R(n-1,kl-1)*R(n-2,kl-1)/b[:n-2]
  v[1:n-1]+=low*vs[-3]/(den*ks[-3])
 vs.append(v);vs=vs[-3:]
 if n in [10,100,1000,3000]:
  kg=math.exp(logG-n*math.log(4)-3*A*n**(1/3)-1.25*math.log(n))
  mass=np.dot(v,phi)
  gam=math.sqrt(2)*mass*kg
  direct=math.exp(logG-n*math.log(4)-3*A*n**(1/3)-.75*math.log(n))*v[0]
  print(n,'mass',mass,'K_c',kg,'canonical_gamma_est',gam,'direct_gamma_est',direct,'orthogonal_norm',np.linalg.norm(v-mass*phi),flush=True)
