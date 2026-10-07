"""Directed interval midpoint integration with explicit second-derivative enclosure.
Core only; tail and exact reduction require independent mathematical audit.
"""
import heapq,itertools
from fractions import Fraction
from interval_decimal import I,D,DN,UP,NEAR,PI,exact_decimal,integer
from airy_interval import A,SQRT3,airy_range
from jet_interval import J,CJ
from real_kernel import kernel as kernel_point
OMEGA=CJ(I(Fraction(-1,2)),SQRT3/2)
ROOT2=I(2).sqrt()
def kernel_jet(z):
 z=J(I(z),1,0);t=z**2;q=t*A
 av,adv,bv,bdv=airy_range(q.v)
 ai=J(av,adv*q.d,q.v*av*q.d**2+adv*q.dd)
 ap=J(adv,q.v*av*q.d,(av+q.v*adv)*q.d**2+q.v*av*q.dd)
 bi=J(bv,bdv*q.d,q.v*bv*q.d**2+bdv*q.dd)
 bp=J(bdv,q.v*bv*q.d,(bv+q.v*bdv)*q.d**2+q.v*bv*q.dd)
 x=ai*bi*(PI/A);r=ai/bi;y=ai**2*(PI/A);p=CJ(x,y)
 v=ap*(2*A)/ai
 ar=r.atan()/r
 gv=J(Fraction(1,2))-t*v/2-v**3/12
 S=(gv*x-t-v**2/2-v/x*ar-2/(3*x**2*(1+r**2)))/A
 u=CJ(bp,ap)*(2*A)/CJ(bi,ai)
 gu=CJ(Fraction(1,2))-u*t/2-u**3/12
 ph=gu*p**2/2+(CJ(t)+u**2/2)*p-u*p.log_q1()-CJ(Fraction(2,3))/p
 num=ph.conj()*4-u.conj()*CJ(0,4*PI/3)-CJ(2*t**2)
 E=(OMEGA*num/CJ(ai,bi)**2).i/PI
 return 2*z*(E-S-2*t/(3*A))+ROOT2/A

def panel(l,h):
 l=exact_decimal(l);h=exact_decimal(h)
 if not D(0)<=l<h<=D('3.2'):raise ValueError('Panel must lie in [0,3.2] with positive width')
 width=I(h)-I(l);mid=NEAR.divide(NEAR.add(l,h),D(2))
 # midpoint is exact for our dyadic refinements of decimal endpoints
 if 2*Fraction(mid)!=Fraction(l)+Fraction(h):raise ValueError("Midpoint rounding is not exact")
 v=kernel_point(I(mid))*width
 dd=kernel_jet(I(l,h)).dd.abs().hi
 rad=(width**3*I(dd)/24).hi
 return v+I(rad.copy_negate(),rad)

def run(tol='0.08',maxpanels=10000):
 tol=exact_decimal(tol);integer(maxpanels,'maximum panel count',64)
 if tol<=0:raise ValueError('Tolerance must be positive')
 count=itertools.count();heap=[];total=I(0)
 for k in range(64):
  l=DN.divide(D(k),D(20));h=DN.divide(D(k+1),D(20));v=panel(l,h);total+=v
  heapq.heappush(heap,(v.width().copy_negate(),next(count),l,h,v))
 steps=0
 while total.width()>D(tol) and len(heap)<maxpanels:
  _,_,l,h,v=heapq.heappop(heap);mid=NEAR.divide(NEAR.add(l,h),D(2));left=panel(l,mid);right=panel(mid,h)
  total=I(DN.add(DN.subtract(total.lo,v.lo),DN.add(left.lo,right.lo)),UP.add(UP.subtract(total.hi,v.hi),UP.add(left.hi,right.hi)))
  for lo,hi,w in [(l,mid,left),(mid,h,right)]:heapq.heappush(heap,(w.width().copy_negate(),next(count),lo,hi,w))
  steps+=1
 if total.width()>tol:raise ValueError('Maximum panel count reached before tolerance')
 out={'status':'PASS','precision':70,'z_interval':['0','3.2'],'t_interval':['0','10.24'],'enclosure':[str(total.lo),str(total.hi)],'panels':len(heap),'quadrature':'midpoint with interval second derivative and width^3/24 remainder'}
 return out,sorted([[str(l),str(h),str(v.lo),str(v.hi)] for _,_,l,h,v in heap],key=lambda row:Fraction(row[0]))
