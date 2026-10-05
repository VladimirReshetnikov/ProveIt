"""Directed rational certificate on |a|=14/25, pi/5<=arg(a)<=pi/2.
No sampled numerical maximum is used. Adaptive boxes cover the full domains.
"""
from fractions import Fraction as F
from pathlib import Path
from functools import lru_cache
import json,time,hashlib
from exact_intervals import I,iv,PI,S,sinp,cosp
from complex_interval_core import C,sqrt_interval
from model_intervals import values,trig_rad
R=F(14,25);J=24;U=F(81,100);CAP=F(19,20)
def require(x,msg):
 if not x:raise ArithmeticError(msg)
def out(x):return [str(F(x.lo,S)),str(F(x.hi,S))]
def flo(x):return F(x.lo,S)
def fhi(x):return F(x.hi,S)
@lru_cache(None)
def cs(x,j):return cosp(x/F(2**j)),sinp(x/F(2**j))
@lru_cache(None)
def hpref(x):
 p=iv(1)
 for j in range(1,J+1):
  c,s=cs(x,j);p=p*(c+R*s)
 return p
def realH(x):
 p=hpref(x);tail=R*PI*x/F(2**J)
 require((PI*x/F(2**(J+1))).hi<iv(R).lo,'positive real tail factors')
 return I(p.lo,(p/(1-tail)).hi)
L=realH(F(1,2));g=R*L;g2=g.square()
require(cosp(F(1,5)).hi<iv(U).lo,'cos(pi/5)<.81')
@lru_cache(None)
def trigbox(l,h,j):
 cl,sl=cs(l,j);ch,sh=cs(h,j)
 c=I(ch.lo,cl.hi)
 s=I(sh.lo,sl.hi) if j==1 else I(sl.lo,sh.hi)
 return c,s

def upperH2(xl,xh,ul,uh,sign):
 u=I(iv(ul).lo,iv(uh).hi);p=iv(1)
 for j in range(1,J+1):
  c,s=trigbox(xl,xh,j)
  f=1-(1-R*R)*s.square()+sign*2*R*u*c*s
  require(f.hi>=0,'nonnegative factor upper')
  p=p*I(0,f.hi)
 tail=R*PI*xh/F(2**J)+(PI*xh).square()/F(6*4**J)
 return p/(1-tail).square()
@lru_cache(None)
def hlower(xl,xh):
 if xh<=F(3,2):yl,yh=xl-1,xh-1
 elif xl>=F(3,2):yl,yh=2-xh,2-xl
 else:raise ArithmeticError('half-integer crossing')
 # Every prefix factor is positive and log concave on [0,1/2].
 return I(min(hpref(yl).lo,hpref(yh).lo),min(hpref(yl).lo,hpref(yh).lo))

def return_box(box):
 xl,xh,ul,uh=box
 den=hlower(xl,xh).square()*g2
 return max(fhi(upperH2(xl,xh,ul,uh,s)/den) for s in [-1,1])
start=time.time();todo=[(F(1),F(3,2),F(0),U),(F(3,2),F(2),F(0),U)];leaves=[];nodes=0;best=F(0)
while todo:
 box=todo.pop();nodes+=1
 ub=return_box(box)
 if ub<CAP*CAP:
  leaves.append([*[str(x) for x in box],str(ub)]);best=max(best,ub);continue
 xl,xh,ul,uh=box
 require(len(leaves)+len(todo)<100000,'return box count guard')
 if 2*(xh-xl)>=uh-ul:
  mid=(xl+xh)/2;todo.extend([(xl,mid,ul,uh),(mid,xh,ul,uh)])
 else:
  mid=(ul+uh)/2;todo.extend([(xl,xh,ul,mid),(xl,xh,mid,uh)])
print('return passed',nodes,len(leaves),float(best),time.time()-start,flush=True)

# Fixed-depth products, squared moduli, all u in [0,.81] and both signs.
shallow=[]
for depth in [1,2,3]:
 top=F(0);cells=[]
 for k in range(32):
  ul=U*k/32;uh=U*(k+1)/32;u=I(iv(ul).lo,iv(uh).hi)
  for sign in [-1,1]:
   p=iv(1)
   for j in range(1,depth+1):
    c,s=cs(F(1),j);f=c.square()+R*R*s.square()+sign*2*R*u*c*s
    p=p*I(0,f.hi)
   val=fhi(p*upperH2(1+F(1,2**depth),1+F(1,2**depth),ul,uh,sign)/g2.square())
   require(val<F(9,25),'shallow ratio <3/5')
   top=max(top,val);cells.append([str(ul),str(uh),sign,str(val)])
 shallow.append({'L':depth,'squared_ratio_upper':str(top),'cells':cells})
print('shallow passed',[float(F(v['squared_ratio_upper'])) for v in shallow],flush=True)

# Deep-depth extension. The two positive angular terms exceed the signed term.
t4=sinp(F(1,32))/cosp(F(1,32));b4=sinp(F(17,64))/cosp(F(17,64))
require(t4.hi<iv(F(1,10)).lo,'t_L<1/10')
require(b4.hi<iv(F(6,5)).lo and R*F(6,5)<1,'two positive factors below one')
negative=R*F(1,10)/(R-F(1,10))**2
positive=2*R/(1+R)**2
require(positive-negative>F(19,100),'deep angular derivative >19/100')
require(PI.square().lo>iv(8).hi,'real log curvature <-2')
# exp(-19/100*(1-U)) <= 1/(1+19/100*(1-U)).
deep_cap=1/(1+F(19,100)*(1-U))

# Principal complex arctangent at rational-angle midpoints, with absolute series tail.
ATAN_N=70
@lru_cache(None)
def atanpoint(q):
 a=C(R*cosp(q),R*sinp(q));aa=a*a;term=a;z=C(iv(0),iv(0))
 for k in range(ATAN_N):
  z=z+term*F((-1)**k,2*k+1);term=term*aa
 rad=iv(R**(2*ATAN_N+1)/((2*ATAN_N+1)*(1-R*R))).hi
 return C(I(z.re.lo-rad,z.re.hi+rad),I(z.im.lo-rad,z.im.hi+rad))
TMIN=F(5371,10000);todo=[(F(1,5),F(1,2))];atanleaves=[];lowall=F(100)
while todo:
 l,h=todo.pop();m=(l+h)/2
 center=sqrt_interval(atanpoint(m).square_mod())
 # Along the circle |d atan(a)/d q|<=pi*R/(1-R²).
 rad=PI*R*(h-l)/(2*(1-R*R))
 lower=center-rad
 if flo(lower)>TMIN:
  lowall=min(lowall,flo(lower));atanleaves.append([str(l),str(h),str(flo(lower))]);continue
 require(h-l>F(1,10**8),'atan subdivision guard')
 todo.extend([(l,m),(m,h)])
print('atan passed',len(atanleaves),float(lowall),flush=True)

# Third saddle at sigma=111/20, independently checked from the model mean.
sigma0=F(111,20);tl=F(423549203,10**9);th=F(423549207,10**9)
ml,gl=values(tl);mh,gh=values(th)
require(3*ml.hi<iv(sigma0).lo and 3*mh.lo>iv(sigma0).hi,'third saddle endpoint bracket')
m43,g43=values(F(43,100));require(3*m43.lo>iv(F(559,100)).hi,'all third saddles below .43')
# atan(R)>.43 by its alternating series, or positive-tan coefficient bound.
a43=trig_rad(F(43,100),True)/trig_rad(F(43,100),False)
require(a43.hi<iv(R).lo,'atan(R)>.43')
# Raise the positive comparison to power20; all powers are exact rational.
eta=F(19,20)
balance=(fhi(g)**2/flo(gl)**3)**20*(th/TMIN)**111
require(balance<eta**20,'uniform third-scale margin eta=19/20')
result={'all_checks_exact':True,'all_checks_passed':True,'radius':str(R),'phase_over_pi':['1/5','1/2'],'product_truncation':J,'precision_scale':str(S),'L_R':out(L),'g_R':out(g),'return_ratio_cap':str(CAP),'return_squared_upper':str(best),'return_nodes':nodes,'return_leaf_count':len(leaves),'return_leaves':leaves,'shallow_ratio_cap':'3/5','shallow':shallow,'deep_angular_derivative_lower':'19/100','deep_uniform_ratio_cap':str(deep_cap),'deep_positive_lower':str(positive),'deep_negative_upper':str(negative),'atan_modulus_lower':str(TMIN),'atan_leaf_count':len(atanleaves),'atan_leaves':atanleaves,'sigma_interval':['111/20','559/100'],'third_saddle_sigma0':[str(tl),str(th)],'third_saddle_mean_left':out(ml),'third_saddle_mean_right':out(mh),'third_model_g_lower':str(flo(gl)),'all_saddles_upper':'43/100','separation_eta':str(eta),'separation_ratio_power20_upper':str(balance),'scope':'Scalar outer arc and template bounds only; no pressure coefficient theorem is claimed.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print('ALL PASS; eta=19/20; elapsed',time.time()-start,flush=True)
