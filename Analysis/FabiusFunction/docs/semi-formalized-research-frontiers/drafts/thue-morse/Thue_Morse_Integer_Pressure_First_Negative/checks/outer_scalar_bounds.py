"""Independent squared-factor replay of an exact outer-contour box certificate.

The producer multiplies complex rectangles. This replay instead multiplies the
exact scalar factors c^2+2 Re(a)c s+|a|^2s^2 and uses log-concave endpoint lower
bounds for the real weight. The prescribed adaptive partition is reconstructed.
"""
from fractions import Fraction as F
from pathlib import Path
from functools import lru_cache
import sys,json,time,hashlib
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT))
from complex_interval_core import I,iv,PI,S,sinp,cosp,trig_rad,tangent_circle
J=20;R=F(2,5)
def ensure(ok,msg):
 if not ok:raise RuntimeError(msg)
@lru_cache(None)
def real_prefix(a,x):
 out=iv(1)
 for j in range(1,J+1):out=out*(cosp(x/F(2**j))+a*sinp(x/F(2**j)))
 return out
# Omitted real factors exceed one: tan(angle/2)<=angle<R for these ranges.
ensure(PI.hi<iv(R*2**(J+2)).lo,'tail monotonicity guard')
Lprefix=real_prefix(R,F(1,2))
ensure(Lprefix.lo>S,'endpoint needed for h>=1')
eps=iv(R)*PI/F(2**(J+1))+(PI/F(2)).square()/F(6*4**J)
LR2=(Lprefix/(1-eps)).square()
@lru_cache(None)
def h_lower(xlo,xhi):
 if xhi<=F(3,2):l=xlo-1;h=xhi-1
 elif xlo>=F(3,2):l=2-xhi;h=2-xlo
 else:raise RuntimeError('crossing half-integer')
 # Positivity and log concavity imply minimum at one of the endpoints.
 low=max(S,min(real_prefix(R,l).lo,real_prefix(R,h).lo))
 return I(low,low)
@lru_cache(None)
def target_g4(t):
 a=trig_rad(t,'sin')/trig_rad(t,'cos')
 # All omitted factors exceed one, even at the smallest real a.
 ensure(a.lo>iv(F(3,10)).hi,'positive a tail guard')
 g=a*real_prefix(a,F(1,2))
 return g.square().square()
@lru_cache(None)
def spatial_trigs(l,h):
 out=[]
 for j in range(1,J+1):
  ll=l/F(2**j);hh=h/F(2**j)
  c=I(cosp(hh).lo,cosp(ll).hi)
  s=I(sinp(hh).lo,sinp(ll).hi) if j==1 else I(sinp(ll).lo,sinp(hh).hi)
  out.append((c,s))
 return out
@lru_cache(None)
def circle(tl,th,ql,qh):return tangent_circle(tl,th,ql,qh)
def upper(box):
 tl,th,ql,qh,xl,xh=box
 a=circle(tl,th,ql,qh);r2=a.square_mod()
 # The entire contour lies in |a|<=tan(t_hi)<2/5, proved by the positive tan series.
 tail=iv(R)*PI*xh/F(2**J)+(PI*xh).square()/F(6*4**J)
 ensure(tail.hi<S,'tail guard')
 tail2=(iv(1)/(1-tail)).square()
 hmax=0
 for sign in [1,-1]:
  prod=iv(1)
  for c,s in spatial_trigs(xl,xh):
   factor=c.square()+r2*s.square()+sign*2*a.re*c*s
   ensure(factor.hi>=0,'negative upper factor')
   prod=prod*I(max(0,factor.lo),factor.hi)
  hmax=max(hmax,(prod*tail2).hi)
 den=h_lower(xl,xh).square()*target_g4(tl)
 ensure(den.lo>0,'denominator positivity')
 return (r2*LR2*I(0,hmax)/den).hi

def replay_partition(leaves,domain):
 tl,th,ql,qh=domain
 rem=set(leaves)
 todo=[(tl,th,ql,qh,F(1),F(3,2)),(tl,th,ql,qh,F(3,2),F(2))]
 nodes=0
 while todo:
  b=todo.pop();nodes+=1
  ensure(nodes<=2*len(leaves)+2,'partition tree cannot match leaves')
  if b in rem:rem.remove(b);continue
  widths=[20*(b[1]-b[0]),3*(b[3]-b[2]),4*(b[5]-b[4])]
  axis=max(range(3),key=lambda i:widths[i]);i=2*axis;mid=(b[i]+b[i+1])/2
  b1=list(b);b2=list(b);b1[i+1]=mid;b2[i]=mid
  todo.extend([tuple(b1),tuple(b2)])
 ensure(not rem,'extra certificate leaves')
 return nodes

