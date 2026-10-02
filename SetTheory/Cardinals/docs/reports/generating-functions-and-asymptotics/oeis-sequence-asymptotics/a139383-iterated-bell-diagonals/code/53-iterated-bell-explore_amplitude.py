import numpy as np
from scipy.special import roots_legendre
import math,json
from pathlib import Path

def psi(z,N):
 t=2/np.array(z,dtype=np.clongdouble)
 for _ in range(N): t=2/np.log1p(2/t)
 L=math.log(N)
 return (t-N+L/3-L/(9*N)+1/(18*N))/(1-1/(3*N))
def calc(N=4000,q=128,r=.5,delta=.02):
 v,w=roots_legendre(q)
 th=(v+1)*math.pi/2; weights=w*math.pi/2
 z=r*np.exp(1j*th)
 arc=np.sum(weights*(z*np.exp(psi(z,N))).real)/math.pi
 bounds=[r]; s=1.
 while s>delta:
  if s<r:bounds.append(s)
  s=-math.expm1(-s)
 bounds.append(delta);bounds.sort()
 vv,ww=roots_legendre(max(24,q//4))
 xs=[];ws=[]
 for a,b in zip(bounds,bounds[1:]):
  xs.extend(a+(vv+1)*(b-a)/2);ws.extend(ww*(b-a)/2)
 xs=np.array(xs);ws=np.array(ws)
 cut=np.sum(ws*np.exp(psi(-xs+1j*1e-100,N)).imag)/math.pi
 arc=float(arc);cut=float(cut)
 return dict(iterations=N,outer_order=q,cut_nodes=len(xs),radius=r,cutoff=delta,outer=arc,cut=cut,I=arc+cut,C=(arc+cut)*math.sqrt(2*math.pi)/2)
rows=[calc(4000,512),calc(16000,512),calc(16000,512,.4)]
print(json.dumps(rows,indent=2));Path(__file__).with_name('contour-longdouble-diagnostics.json').write_text(json.dumps({'not_certified':True,'rows':rows},indent=2))
