"""Independent rational stress, series, and derivative checks; no external libraries."""
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal as D,getcontext,Inexact,Rounded,FloatOperation
import sys,random,json
HERE=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.path.insert(0,str(HERE))
from interval_decimal import I,PI,gamma_fraction
from airy_interval import fundamental_point,atan_point,C,airy_point,airy_range,AI0,AP0
from jet_interval import J,CJ
from real_kernel import kernel
from integrate_core import kernel_jet,panel
rng=random.Random(42100264);count=0
def incl(box,q):
 global count
 if not F(box.lo)<=q<=F(box.hi):raise ValueError(('inclusion',box,q))
 count+=1
def within(box,l,h):
 incl(box,l);incl(box,h)
def dec():
 sign='-' if rng.randrange(2) else ''
 return D(sign+''.join(str(rng.randrange(10)) for _ in range(95))+'e-'+str(rng.randrange(80,110)))
for _ in range(180):
 a=I(*sorted([dec(),dec()]));b=I(*sorted([dec(),dec()]))
 xs=[F(a.lo),F(a.hi),(F(a.lo)+F(a.hi))/2]
 ys=[F(b.lo),F(b.hi),(F(b.lo)+F(b.hi))/2]
 for x in xs:
  incl(-a,-x);incl(a.abs(),abs(x))
  for n in [0,1,2,3,7,12]:incl(a**n,x**n)
  for y in ys:
   incl(a+b,x+y);incl(a-b,x-y);incl(a*b,x*y)
   if not b.lo<=0<=b.hi:incl(a/b,x/y)
 for x in xs:
  if not a.lo<=0<=a.hi:
   incl(a.inv(),1/x);incl(a**-3,x**-3)

def alt_atan(x,n=800):
 s=F(0);term=x
 for k in range(n):
  s+=((-1)**k)*term/(2*k+1);term*=x*x
 nxt=((-1)**n)*term/(2*n+1)
 return min(s,s+nxt),max(s,s+nxt)
pl,ph=alt_atan(F(1,5),160);ql,qh=alt_atan(F(1,239),50)
pil,pih=16*pl-4*qh,16*ph-4*ql
within(PI,pil,pih)
for text in ['0','0.00000000000000000000000000000000000000001','.001','.099','.1','.1001','.25','.5','.5774','1','2','100']:
 x=F(text);sgn=-1 if x<0 else 1;y=abs(x)
 if y==1:l,h=pil/4,pih/4
 elif y>1:
  l0,h0=alt_atan(1/y);l,h=pil/2-h0,pih/2-l0
 else:l,h=alt_atan(y)
 if sgn<0:l,h=-h,-l
 within(atan_point(D(text)),l,h)
for arg in [I(-2,-1),I(-2),I('-.5'),I(-1,1)]:
 try:atan_point(arg)
 except ValueError:count+=1
 else:raise ValueError('negative arctangent helper input accepted')

def independent_basis(x,offset,nterms=88):
 # Construct exact power-series coefficients from c_(m+2)=c_(m-1)/((m+2)(m+1)).
 co=[F(0)]*(3*nterms+offset+4);co[offset]=F(1)
 for j in range(offset+3,len(co),3):co[j]=co[j-3]/(j*(j-1))
 last=offset+3*nterms
 val=sum((co[j]*x**j for j in range(last+1)),F(0))
 der=sum((j*co[j]*x**(j-1) for j in range(1,last+1)),F(0))
 n=last+3;first=co[n]*x**n
 ratio=x**3/F((n+3)*(n+2))
 dratio=ratio*F(n+3,n)
 tail=first/(1-ratio)
 dtail=F(0) if x==0 else n*first/x/(1-dratio)
 return val,val+tail,der,der+dtail
for text in ['0','.05','1','4','8','9']:
 for off in [0,1]:
  box,d= fundamental_point(D(text),off)
  l,h,dl,dh=independent_basis(F(text),off)
  within(box,l,h);within(d,dl,dh)

def jcheck(j,a):
 for v,q in zip((j.v,j.d,j.dd),(a[0],a[1],2*a[2])):incl(v,q)
def padd(a,b):return [x+y for x,y in zip(a,b)]
def pmul(a,b):return [sum((a[j]*b[k-j] for j in range(k+1)),F(0)) for k in range(3)]
def pinv(a):
 out=[1/a[0]]
 for k in range(1,3):out.append(-sum((a[j]*out[k-j] for j in range(1,k+1)),F(0))/a[0])
 return out
for _ in range(150):
 a=[F(rng.randrange(1,200),10)]+[F(rng.randrange(-100,101),10) for _ in range(2)]
 b=[F(rng.randrange(1,200),10)]+[F(rng.randrange(-100,101),10) for _ in range(2)]
 ja=J(I(a[0]),I(a[1]),I(2*a[2]));jb=J(I(b[0]),I(b[1]),I(2*b[2]))
 jcheck(ja+jb,padd(a,b));jcheck(ja*jb,pmul(a,b));jcheck(ja.inv(),pinv(a));jcheck(ja/jb,pmul(a,pinv(b)))
 po=[F(1),F(0),F(0)]
 for n in range(8):jcheck(ja**n,po);po=pmul(po,a)
 for n in [1,2,3]:
  po=[F(1),F(0),F(0)]
  for _ in range(n):po=pmul(po,pinv(a))
  jcheck(ja**(-n),po)
 logarithm=ja.ln();incl(logarithm.d,a[1]/a[0]);incl(logarithm.dd,2*a[2]/a[0]-(a[1]/a[0])**2)
 arctan=ja.atan();incl(arctan.d,a[1]/(1+a[0]**2));incl(arctan.dd,2*a[2]/(1+a[0]**2)-2*a[0]*a[1]**2/(1+a[0]**2)**2)

def ca(a,b):return (a[0]+b[0],a[1]+b[1])
def cm(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def ci(a):return (a[0]/(a[0]**2+a[1]**2),-a[1]/(a[0]**2+a[1]**2))
def cs(a,s):return (a[0]*s,a[1]*s)
def cc(c,q):incl(c.r,q[0]);incl(c.i,q[1])
def cpmul(a,b):
 result=[]
 for k in range(3):
  q=(F(0),F(0))
  for j in range(k+1):q=ca(q,cm(a[j],b[k-j]))
  result.append(q)
 return result
def cpinv(a):
 out=[ci(a[0])]
 for k in range(1,3):
  q=(F(0),F(0))
  for j in range(1,k+1):q=ca(q,cm(a[j],out[k-j]))
  out.append(cs(cm(q,ci(a[0])),-1))
 return out
def cjcheck(c,a):
 for v,q in zip((C(c.r.v,c.i.v),C(c.r.d,c.i.d),C(c.r.dd,c.i.dd)),(a[0],a[1],cs(a[2],2))):cc(v,q)
for _ in range(100):
 a=[(F(rng.randrange(1,100),10),F(rng.randrange(1,100),10)) for _ in range(3)]
 c=C(I(a[0][0]),I(a[0][1]));cc(c.inv(),ci(a[0]));cc(c*c,cm(a[0],a[0]))
 cj=CJ(J(I(a[0][0]),I(a[1][0]),I(2*a[2][0])),J(I(a[0][1]),I(a[1][1]),I(2*a[2][1])))
 cjcheck(cj.inv(),cpinv(a));cjcheck(cj*cj,cpmul(a,a))
 log=cj.log_q1();first=cm(a[1],ci(a[0]));second=ca(cm(cs(a[2],2),ci(a[0])),cs(cm(first,first),-1))
 cc(C(log.r.d,log.i.d),first);cc(C(log.r.dd,log.i.dd),second)

# Normalization checks constrain the Gamma construction beyond a digits comparison.
incl(gamma_fraction(F(1)),F(1));incl(gamma_fraction(F(2)),F(1));incl(gamma_fraction(F(5)),F(24))
# Sqrt bounds can be checked by exact squaring, independent of Decimal.sqrt accuracy.
for q in [F(0),F(1,100),F(2),F(3),F(100001,17)]:
 s=I(q).sqrt()
 if F(s.hi)<0 or F(s.hi)**2<q:raise ValueError('sqrt upper')
 if s.lo>0 and F(s.lo)**2>q:raise ValueError('sqrt lower')
 count+=1

# Trap all default-context rounding in proof-valued operations; heap scheduling is separate.
points=['0','.1','1','2','3.2']
before=[(repr(kernel(I(z))),repr(kernel_jet(I(z)))) for z in points]
getcontext().prec=6;getcontext().traps[Inexact]=True;getcontext().traps[Rounded]=True;getcontext().traps[FloatOperation]=True
after=[(repr(kernel(I(z))),repr(kernel_jet(I(z)))) for z in points]
if before!=after:raise ValueError('proof output depends on default context')
panel(D('1.03125'),D('1.034375'))
print(json.dumps({'status':'PASS','independent_exact_inclusions_and_checks':count,'proof_kernel_default_context_traps':'PASS'},sort_keys=True,indent=2))
