"""Logarithmic spatial derivative sharpening of the scalar outer bound."""
from fractions import Fraction as F
from functools import lru_cache
from outer_scalar_bounds import I,iv,PI,S,sinp,cosp,R,J,LR2,real_prefix,target_g4,circle,spatial_trigs,ensure,upper as direct_upper

# A uniform bound for omitted logarithmic derivatives, squared H and squared h.
def log_tail_bound(xmax):
 tau=PI*xmax/F(2**(J+1))
 return 2*PI/F(2**J)*(R+tau)/(1-R*tau-tau.square()/2)
TAIL_D=log_tail_bound(F(2))+log_tail_bound(F(1,2))
@lru_cache(None)
def h_derivative(l,h):
 if h<=F(3,2):xl=l-1;xh=h-1;sign=1
 elif l>=F(3,2):xl=2-h;xh=2-l;sign=-1
 else:raise ArithmeticError('crossed midpoint')
 z=iv(0)
 for j in range(1,J+1):
  ll=xl/F(2**j);hh=xh/F(2**j)
  c=I(cosp(hh).lo,cosp(ll).hi);s=I(sinp(ll).lo,sinp(hh).hi)
  z=z+PI/F(2**j)*(R*c-s)/(c+R*s)
 return sign*2*z
@lru_cache(None)
def h_point_lower(x):
 y=min(x-1,2-x)
 low=max(S,real_prefix(R,y).lo)
 return I(low,low)

def sharp_upper(box):
 tl,th,ql,qh,xl,xh=box
 a=circle(tl,th,ql,qh);r2=a.square_mod();xm=(xl+xh)/2;rad=(xh-xl)/2
 tail=iv(R)*PI*xm/F(2**J)+(PI*xm).square()/F(6*4**J)
 tail2=(iv(1)/(1-tail)).square()
 denpoint=h_point_lower(xm).square()
 Dden=h_derivative(xl,xh)
 maximum=0
 for sign in [1,-1]:
  u=sign*a.re;prod=iv(1);D=iv(0)
  for j,((c,s),(cm,sm)) in enumerate(zip(spatial_trigs(xl,xh),spatial_trigs(xm,xm)),1):
   norm=c.square()+r2*s.square()+2*u*c*s
   if norm.lo<=0:raise ArithmeticError('uncertain spatial zero')
   normm=cm.square()+r2*sm.square()+2*u*cm*sm
   ensure(normm.hi>=0,'negative midpoint bound')
   prod=prod*I(max(0,normm.lo),normm.hi)
   D=D+2*PI/F(2**j)*(u*(c.square()-s.square())+(r2-1)*c*s)/norm
  D=D-Dden+I(-TAIL_D.hi,TAIL_D.hi)
  lips=I(0,max(abs(D.lo),abs(D.hi)))*rad
  if lips.hi>=S:raise ArithmeticError('large exponential increment')
  ratio=prod*tail2/denpoint/(1-lips)
  maximum=max(maximum,ratio.hi)
 return (r2*LR2*I(0,maximum)/target_g4(tl)).hi

def best_upper(box):
 val=direct_upper(box)
 try:val=min(val,sharp_upper(box))
 except (ArithmeticError,ValueError):pass
 return val
