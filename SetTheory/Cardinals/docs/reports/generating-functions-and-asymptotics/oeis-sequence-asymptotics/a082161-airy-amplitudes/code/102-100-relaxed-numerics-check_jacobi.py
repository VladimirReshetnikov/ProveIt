"""Optional floating-point spectral diagnostics, not proof or interval certificates."""
import numpy as np
from scipy.linalg import eigh_tridiagonal
from scipy.special import airy,ai_zeros
from math import sqrt
A=ai_zeros(2)[0]
a=A[0]
prev=None
for n in (100,1000,10000,100000):
 k=np.arange(n+1,dtype=float)
 D=(2*n-2*k+1)/(n+k);D[0]=1
 b=(n-k[1:]+1)/np.sqrt((n+k[1:])*(n+k[1:]-1))
 vals,vec=eigh_tridiagonal(D,b,select='i',select_range=(n-1,n))
 lam=vals[-1];phi=vec[:,-1];phi*=np.sign(phi[0])
 ep=n**(-1/3);x=ep*(k+.5)
 q=ep**.5*sqrt(2)*airy(2*x+a)[0]/airy(a)[1];q/=np.linalg.norm(q)
 Jq=D*q;Jq[1:]+=b*q[:-1];Jq[:-1]+=b*q[1:]
 residual=np.linalg.norm(Jq-(4+4*a*ep**2+6*ep**3)*q)
 # Drift at consecutive dimensions.
 m=n-1;j=np.arange(m+1,dtype=float)
 D0=(2*m-2*j+1)/(m+j);D0[0]=1
 b0=(m-j[1:]+1)/np.sqrt((m+j[1:])*(m+j[1:]-1))
 p0=eigh_tridiagonal(D0,b0,select='i',select_range=(m,m))[1][:,0];p0*=np.sign(p0[0]);p0=np.r_[p0,0]
 R=np.zeros(n+1);R[:-1]=(n-k[:-1])/n*np.sqrt((n+k[:-1]-1)*(n+k[:-1])/(n*(n-1)))
 print(dict(n=n, lambda_remainder=(lam-4-4*a*ep**2-6*ep**3)/ep**4,
            gap_scaled=(lam-vals[-2])/ep**2,
            endpoint_scaled=phi[0]*sqrt(n),
            endpoint_rel_error_scaled=(phi[0]*sqrt(n/2)-1)/ep**2,
            quasimode_residual_scaled=residual/ep**4,
            phi_error_scaled=np.linalg.norm(phi-q)/ep**2,
            drift_scaled=n*np.linalg.norm(phi-p0),
            gauge_defect_scaled=np.linalg.norm((1-R)*phi)/ep**4))
