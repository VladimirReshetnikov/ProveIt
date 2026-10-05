"""Exact scalar certificate for the new radius-one-half Green norm."""
from fractions import Fraction as F
from dataclasses import dataclass
from math import factorial
from pathlib import Path
import json,time
def need(b,message):
 if not b: raise ArithmeticError(message)
S=10**32
@dataclass(frozen=True)
class I:
 lo:int;hi:int
 def __add__(a,b):
  if not isinstance(b,I):b=iv(b)
  return I(a.lo+b.lo,a.hi+b.hi)
 __radd__=__add__
 def __neg__(a):return I(-a.hi,-a.lo)
 def __sub__(a,b):return a+-iv(b)
 def __rsub__(a,b):return iv(b)+-a
 def __mul__(a,b):
  b=iv(b);v=[a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi];return I(min(v)//S,-((-max(v))//S))
 __rmul__=__mul__
 def __truediv__(a,b):
  if not isinstance(b,I):
   b=F(b);need(b>0,"positive scalar denominator")
   return I((a.lo*b.denominator)//b.numerator,-((-a.hi*b.denominator)//b.numerator))
  need(b.lo>0,"positive interval denominator");return a*I(S*S//b.hi,-((-S*S)//b.lo))
 def square(a):
  lo=0 if a.lo<=0<=a.hi else min(a.lo*a.lo,a.hi*a.hi)
  hi=max(a.lo*a.lo,a.hi*a.hi);return I(lo//S,-((-hi)//S))
def iv(x):
 if isinstance(x,I):return x
 x=F(x);return I((x.numerator*S)//x.denominator,-((-x.numerator*S)//x.denominator))
def atan_bounds(q,N):
 v=sum((F((-1)**k,(2*k+1)*q**(2*k+1))for k in range(N)),F(0));w=v+F((-1)**N,(2*N+1)*q**(2*N+1));return min(v,w),max(v,w)
a,b=atan_bounds(5,32);c,d=atan_bounds(239,10);plo,phi=16*a-4*d,16*b-4*c
PI=I(iv(plo).lo,iv(phi).hi)
def sinp(x):
 x=PI*iv(x);xx=x.square();term=x;v=x
 for k in range(1,40):term=-(term*xx)/((2*k)*(2*k+1));v=v+term
 # Taylor's derivative remainder: |R_80(x)|<=|x|^81/81!; degree79 used, so use degree80 with zero coefficient.
 ab=I(0,max(abs(x.lo),abs(x.hi)));power=iv(1)
 for _ in range(81):power=power*ab
 rad=(power/ factorial(81)).hi;return I(v.lo-rad,v.hi+rad)
def cosp(x):
 x=PI*iv(x);xx=x.square();term=iv(1);v=term
 for k in range(1,40):term=-(term*xx)/((2*k-1)*(2*k));v=v+term
 # Degree78 polynomial equals degree79 Taylor polynomial.
 ab=I(0,max(abs(x.lo),abs(x.hi)));power=iv(1)
 for _ in range(80):power=power*ab
 rad=(power/factorial(80)).hi;return I(v.lo-rad,v.hi+rad)
def srng(l,h,mode):
 # Required intervals are contained in a monotonicity interval.
 a,b=sinp(l),sinp(h)
 return I(a.lo,b.hi) if mode=='up' else I(b.lo,a.hi)
def crng(l,h):return I(cosp(h).lo,cosp(l).hi)

r=F(1,2);K=20

def H(x):
 p=iv(1)
 for j in range(1,K+1): p=p*(cosp(x/F(2**j))+r*sinp(x/F(2**j)))
 tail=r*PI*iv(x/F(2**K))
 need(tail.hi<S,"product tail")
 need((PI*iv(x/F(2**(K+1)))).hi<iv(r/2).lo,"positive omitted factors")
 return I(p.lo,(p/(1-tail)).hi)

def hp(x):
 v=iv(0)
 for j in range(1,K+1):
  ss=sinp(x/F(2**j));cc=cosp(x/F(2**j))
  v=v+(PI/F(2**j))*((-ss+r*cc)/(cc+r*ss))
 return I(v.lo,(v+r*PI/F(2**K)).hi)

def strict_less(x,q,label):need(x.hi<iv(q).lo,label)
def strict_more(x,q,label):need(x.lo>iv(q).hi,label)
def out(x):return [str(F(x.lo,S)),str(F(x.hi,S))]
L=H(F(1,2));H38=H(F(3,8));hp14=hp(F(1,4));hp38=hp(F(3,8));hp12=hp(F(1,2))
strict_more(L,1,"L>1");strict_less(L,F(7,5),"L<7/5")
strict_less(H38,F(7,5),"H(3/8)<7/5")
strict_more(hp14,0,"increasing on first quarter")
strict_more(hp38,0,"positive tangent slope")
strict_less(hp38,F(6,25),"tangent slope <.24")
strict_more(hp12,F(-1,5),"ellprime >-.2")
need(F(7,5)/(1-F(3,100))<F(3,2),"envelope via exponential tangent")
# On x in [u,v], ellprime decreases and the first trig term decreases.
# Thus these eight endpoint inequalities prove b_minus strictly increasing.
monotone=[]
for i in range(8):
 u=F(i,16);v=F(i+1,16)
 ss=sinp(v/2);cc=cosp(v/2)
 low=PI/2*((cc-r*ss)/(ss+r*cc))-hp((1-v)/2)/2-hp(u)
 strict_more(low,0,"bminus derivative cell "+str(i))
 monotone.append(out(low))
x=F(2,5);ss=sinp(x/2);cc=cosp(x/2)
bminus=(ss+r*cc)*H((1-x)/2)/H(x)
pminus=(cc-r*ss)/(cc+r*ss)
strict_less(bminus,F(97,100),"bminus(.4)<.97")
strict_less(pminus,F(47,100),"pminus(.4)<.47")
strict_less(r*L,F(7,10),"rL<.7")
strict_less(PI,F(16,5),"pi<16/5")
strict_less(9*PI/8,4,"weight derivative constant")
strict_less(PI/2,2,"projection derivative constant")
# Two-row contraction and monotone continuation.
d0=256;gamma=F(9,10);theta=F(19,20);tau=F(97,100)
alpha=F(3,4)+(4*d0+13)*gamma**d0+F(19,2)*tau**d0
beta=F(1,2)+F(1,2)*tau**d0
row0=alpha+6*theta**d0
row1=beta+F(d0,2)*(gamma/theta)**d0
need(row0<F(4,5) and row1<F(4,5),"both contraction rows")
need(gamma*F(4*d0+17,4*d0+13)<1,"alpha monotone")
need(gamma/theta*F(d0+1,d0)<1,"row1 monotone")
result={"radius":"1/2","cutoff_d":d0,"scale":str(S),"product_truncation":K,
 "L_interval":out(L),"H_three_eighths":out(H38),"ellprime_quarter":out(hp14),
 "ellprime_three_eighths":out(hp38),"ellprime_half":out(hp12),
 "bminus_derivative_lower_cells":monotone,"bminus_two_fifths":out(bminus),
 "pminus_two_fifths":out(pminus),"row0":str(row0),"row1":str(row1),
 "all_comparisons_exact":True,"all_comparisons_passed":True}
Path(__file__).with_name('scalar_certificate.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['row0','row1','bminus_derivative_lower_cells']},indent=2))
