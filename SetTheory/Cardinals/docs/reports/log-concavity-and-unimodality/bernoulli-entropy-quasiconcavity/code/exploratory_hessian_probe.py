import numpy as np
from scipy.linalg import eigvalsh

def pmf_jet(p):
 n=len(p)
 f=np.zeros(n+1);f[0]=1
 d=np.zeros((n,n+1));h=np.zeros((n,n,n+1))
 for i,a in enumerate(p):
  shiftf=np.roll(f,1);shiftf[0]=0
  shiftd=np.roll(d,1,axis=1);shiftd[:,0]=0
  shifth=np.roll(h,1,axis=2);shifth[:,:,0]=0
  h=(1-a)*h+a*shifth
  h[i,:,:]+=shiftd-d;h[:,i,:]+=shiftd-d
  d=(1-a)*d+a*shiftd
  d[i,:]+=shiftf-f
  f=(1-a)*f+a*shiftf
 return f,d,h

def ehess(p,q,kind='T'):
 f,d,h=pmf_jet(p)
 w=f**(q-2)
 th=q*((q-1)*(d*w)@d.T+np.einsum('ijk,k->ij',h,f**(q-1)))
 if kind=='T':return -th/(q-1)
 t=sum(f**q);g=q*d@(f**(q-1))
 return -(th/t-np.outer(g,g)/t**2)/(q-1)
if __name__=='__main__':
 rng=np.random.default_rng(5896)
 for q,kind in [(3.65,'T'),(3.5,'T'),(3.,'T'),(2.,'R')]:
  best=(-1e9,None)
  for n in [2,3,4,5,8,12,20]:
   for j in range(300):
    p=rng.beta(.25,.25,n) if j<150 else rng.uniform(.001,.999,n)
    v=eigvalsh(ehess(p,q,kind))[-1]
    if v>best[0]:best=(v,p.tolist())
   print(q,kind,n,best,flush=True)
