"""Exploratory finite diagnostics. These are NOT interval certificates."""
import numpy as np
from scipy.special import roots_legendre
import math,json
from pathlib import Path
from mpmath import mp
mp.dps=40

def psi(z,N):
 t=2/np.array(z,dtype=np.clongdouble)
 for _ in range(N):t=2/np.log1p(2/t)
 # Invert the known first orbit correction; numerical only.
 L=math.log(N)
 return (t-N+L/3-L/(9*N)+1/(18*N))/(1-1/(3*N))

def contour(N=8000,q=512):
 v,w=roots_legendre(q); th=(v+1)*math.pi/2
 z=.5*np.exp(1j*th); aw=w/2
 bounds=[.5];s=1.
 while s>.01:
  if s<.5:bounds.append(s)
  s=-math.expm1(-s)
 bounds.append(.01);bounds.sort()
 vv,ww=roots_legendre(128);xs=[];ws=[]
 for a,b in zip(bounds,bounds[1:]):
  xs.extend(a+(vv+1)*(b-a)/2);ws.extend(ww*(b-a)/2/math.pi)
 xs=np.array(xs);ws=np.array(ws)
 pa=psi(z,N);pc=psi(-xs+1j*1e-100,N)
 out={}
 for lam in [.5,1.,2.]:
  beta=1/lam
  moments=[float(np.sum(aw*(z*np.exp(beta*pa)*pa**j).real)+np.sum(ws*(np.exp(beta*pc)*pc**j).imag)) for j in range(3)]
  out[lam]=moments
 return out

mom=contour();N=160;maxm=2*N
S=[[0]*(N+1) for _ in range(N+1)];S[0][0]=1
for n in range(1,N+1):
 for k in range(1,n+1):S[n][k]=k*S[n-1][k]+S[n-1][k-1]
h=[0]*(N+1);h[1]=1;counts={}
for m in range(1,maxm+1):
 h=[0]+[sum(S[n][k]*h[k] for k in range(1,n+1)) for n in range(1,N+1)]
 for n in [39,40,79,80,159,160]:
  for lam in [.5,1.,2.]:
   if m==int(lam*n):counts[(n,lam)]=h[n]
rows=[]
for (n,lam),value in sorted(counts.items()):
 beta=1/lam;I,m1,m2=mom[lam];mu1=m1/I;mu2=m2/I
 delta=math.floor(lam*n)-lam*n
 L=math.log(n);A=delta-(L+math.log(lam))/3
 P1=1/12-beta**2*((mu2+2*A*mu1+A*A)/2+(mu1+A)/3+1/18)
 logscale=mp.log(2*mp.pi)/2+(2*n-mp.mpf(1)/2-beta/3)*mp.log(n)+n*mp.log(lam/(2*mp.e))-beta*mp.log(lam)/3+beta*delta
 normalized=float(mp.exp(mp.log(value)-logscale))
 ratio=normalized/I
 rows.append(dict(n=n,lambda_=lam,depth=math.floor(lam*n),delta=delta,I_estimate=I,normalized_count=normalized,leading_ratio=ratio,first_corrected_ratio=ratio/(1+P1/n)))
result={'not_certified':True,'method':'long-double fixed contour quadrature plus exact integer recurrence','moments':mom,'rows':rows}
Path(__file__).with_name('diagnostics.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
