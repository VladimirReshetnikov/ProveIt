from fractions import Fraction as F
from functools import lru_cache
from math import factorial
from exact_intervals import I,iv,PI,S,sinp,cosp
from complex_interval_core import C,sqrt_interval
from model_intervals import trig_rad,values

def need(ok,msg):
 if not ok:raise ArithmeticError(msg)
need(8*2**80*S<factorial(80),'hyperbolic Taylor remainder below one grid unit')

def flo(x):return F(x.lo,S)
def fhi(x):return F(x.hi,S)
def hull(xl,xh):return I(iv(xl).lo,iv(xh).hi)
@lru_cache(None)
def cs(x,j):return cosp(x/F(2**j)),sinp(x/F(2**j))
@lru_cache(None)
def hyper(x,odd):
 x=iv(x);need(0<=x.lo and x.hi<2*S,'hyper argument');xx=x.square();term=x if odd else iv(1);val=term
 for j in range(1,40):
  term=term*xx/((2*j)*(2*j+1)if odd else(2*j-1)*(2*j));val=val+term
 return I(val.lo-1,val.hi+1)
def tangent_box(tl,th,ql,qh):
 co=I(max(0,cosp(qh).lo),min(S,cosp(ql).hi));si=I(max(0,sinp(ql).lo),min(S,sinp(qh).hi));t=hull(tl,th);u=2*t*co;v=2*t*si
 need(u.lo>=0 and v.lo>=0 and u.hi<(PI/2).lo and v.hi<2*S,'monotone tangent argument ranges')
 ul,uh=flo(u),fhi(u);vl,vh=flo(v),fhi(v)
 ss=I(trig_rad(ul,True).lo,trig_rad(uh,True).hi);cc=I(trig_rad(uh,False).lo,trig_rad(ul,False).hi)
 sh=I(hyper(vl,True).lo,hyper(vh,True).hi);ch=I(hyper(vl,False).lo,hyper(vh,False).hi)
 den=cc+ch;return C(ss/den,sh/den)
J=24

def H2_box(a,x,R):
 rr=a.square_mod();rr=I(max(0,rr.lo),min(iv(R*R).hi,rr.hi));p=iv(1)
 for j in range(1,J+1):
  c,s=cs(x,j);f=c.square()+rr*s.square()+2*a.re*c*s;p=p*I(max(0,f.lo),f.hi)
 tail=R*PI*x/F(2**J)+(PI*x).square()/F(6*4**J)
 upper=p/(1-tail).square()
 return I(0,upper.hi) # Only an upper bound for the infinite modulus is asserted.
@lru_cache(None)
def glower(t):return values(t)[1]

def exp_small(x):
 x=iv(x);need(0<=x.lo and x.hi<2*S,'exp argument');term=iv(1);z=term
 for j in range(1,41):term=term*x/j;z=z+term
 # e^2*2^41/41! < 1/S; use e^2<8.
 need(8*2**41*S<factorial(41),'exp remainder')
 return I(z.lo-1,z.hi+1)

def atan_center(a,R=F(14,25)):
 aa=a*a;term=a;z=C(iv(0),iv(0));N=70
 for k in range(N):z=z+term*F((-1)**k,2*k+1);term=term*aa
 rad=iv(R**(2*N+1)/((2*N+1)*(1-R*R))).hi
 return C(I(z.re.lo-rad,z.re.hi+rad),I(z.im.lo-rad,z.im.hi+rad))
