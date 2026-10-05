"""Adaptive exact scalar predicates for a fixed complex renewal corridor.
No acceptance decision uses floating point. The parameter rectangle is
.45<=Re a<=.50, 0<=Im(a)^2<=.1089; conjugation covers the lower half.
"""
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import json,time
from exact_intervals import I,iv,PI,S,sinp,cosp

def need(ok,msg):
 if not ok:raise ArithmeticError(msg)
def box(l,h):return I(iv(l).lo,iv(h).hi)
@lru_cache(None)
def trigbox(l,h,j):
 l=l/F(2**j);h=h/F(2**j)
 cc=I(cosp(h).lo,cosp(l).hi)
 lo=min(sinp(l).lo,sinp(h).lo)
 hi=max(sinp(l).hi,sinp(h).hi)
 if l<=F(1,2)<=h:hi=S
 return cc,I(lo,hi)
J=20
@lru_cache(None)
def Hsq(ul,uh,wl,wh,xl,xh,sign=1):
 u=box(ul,uh);w=box(wl,wh);p=iv(1)
 for j in range(1,J+1):
  c,s=trigbox(xl,xh,j)
  z=c+sign*u*s;p=p*(z.square()+w*s.square())
 if sign<0:return I(0,p.hi) # Every omitted factor has modulus<=1.
 eps=F(3,5)*PI*iv(xh/F(2**J))+(PI*iv(xh)).square()/F(6*4**J)
 need(eps.hi<S,'product tail')
 # Positive real parts imply each omitted modulus exceeds one.
 need((PI*iv(xh/F(2**(J+1)))).hi<iv(F(9,40)).lo,'positive omitted factors')
 return I(p.lo,(p/(1-eps).square()).hi)
@lru_cache(None)
def hp(u,w,x):
 p=iv(0)
 for j in range(1,J+1):
  c,s=trigbox(x,x,j)
  p=p+(PI/F(2**j))*(((iv(u)*c-s)*(c+iv(u)*s)+iv(w)*c*s)/((c+iv(u)*s).square()+iv(w)*s.square()))
 err=(PI/F(2**J)).hi
 return I(p.lo-err,p.hi+err)
# Monotone field/x reductions in the written proof reduce derivatives to1D/2D.
der=[]
for j in range(64):
 l=F(j,128);h=F(j+1,128)
 B=hp(F(1,2),F(1089,10000),l)+hp(F(1,2),F(1089,10000),1-h)
 need(B.hi<0,'bminus derivative '+str(j));der.append(['bminus',j,str(F(B.hi,S))])
 for k in range(8):
  wl=F(1089*k,80000);wh=F(1089*(k+1),80000);u=F(9,20)
  c,s=trigbox(l,h,1)
  T=((s+u*c)*(c-u*s)-wh*c*s)/((c-u*s).square()+wh*s.square())
  D=-PI/2*T-hp(u,wl,1-l/2)/2-hp(u,wl,h)
  need(D.hi<0,'right-edge derivative '+str((j,k)));der.append(['right_edge',j,k,str(F(D.hi,S))])
print('Derivative cells passed',len(der),flush=True)
# Global field extrema used by the adapted norm.
gmax=Hsq(F(1,2),F(1,2),F(1089,10000),F(1089,10000),F(1),F(1))
gmin=Hsq(F(9,20),F(9,20),F(0),F(0),F(1),F(1))
need(gmax.hi<iv(F(9,10)**2).lo,'g upper')
need(gmin.lo>iv(F(29,50)**2).hi,'g lower')
need(Hsq(F(9,20),F(9,20),F(0),F(0),F(1,2),F(1,2)).lo>iv(F(13,10)**2).hi,'h half lower')
need(hp(F(9,20),F(0),F(1,4)).lo>0,'first-quarter increase')
need(hp(F(9,20),F(0),F(1,2)).lo>iv(F(-1,2)).hi,'logarithmic derivative lower')
need((sinp(F(1,16))/cosp(F(1,16))).hi<iv(F(1,5)).lo,'near secondary tangent bound')
# Each task has an exact squared-ratio target. Normalized cell coordinates
# map affinely to the compact field rectangle and the stated spatial range.
tasks={
 'Q_middle':(F(1,16),F(1,2),F(99,100)**2),
 'opposite_outer':(F(1),F(2),F(99,100)**2),
 'opposite_variation':(F(0),F(1,2),F(9,10)**2),
 'bplus_far':(F(1,8),F(1,2),F(99,100)**2),
 'opposite_template_deep':(F(1),F(5,4),F(9,10)**2),
 'opposite_template_shallow':(F(0),F(0),F(9,10)**2),
 'opposite_pulse':(F(0),F(0),F(9,10)**2),
}
def bound(name,ends):
 ul=F(9,20)+ends[0]/20;uh=F(9,20)+ends[1]/20
 wl=F(1089,10000)*ends[2];wh=F(1089,10000)*ends[3]
 xl0,xh0,_=tasks[name];xl=xl0+(xh0-xl0)*ends[4];xh=xl0+(xh0-xl0)*ends[5]
 g=Hsq(ul,uh,wl,wh,F(1),F(1));u=box(ul,uh);w=box(wl,wh)
 if name=='Q_middle':return Hsq(ul,uh,wl,wh,1+xl,1+xh)/(g*Hsq(ul,uh,wl,wh,xl,xh))
 if name=='opposite_outer':
  if xh<=F(3,2):dl,dh=xl-1,xh-1
  elif xl>=F(3,2):dl,dh=2-xh,2-xl
  else:dl=min(xl-1,2-xh);dh=F(1,2)
  return Hsq(ul,uh,wl,wh,xl,xh,-1)/(g*Hsq(ul,uh,wl,wh,dl,dh))
 if name=='opposite_variation':return Hsq(ul,uh,wl,wh,1-xh,1-xl,-1)/(g.square()*Hsq(ul,uh,wl,wh,xl,xh))
 if name=='bplus_far':
  c,s=trigbox(xl,xh,1);factor=(s-u*c).square()+w*c.square()
  return factor*Hsq(ul,uh,wl,wh,(1-xh)/2,(1-xl)/2)/(g*Hsq(ul,uh,wl,wh,xl,xh))
 if name=='opposite_template_deep':
  c,s=trigbox(F(1),F(1),2);pref=(u.square()+w)*((c-u*s).square()+w*s.square())
  return pref*Hsq(ul,uh,wl,wh,xl,xh,-1)/(g*g*g)
 if name=='opposite_template_shallow':return (u.square()+w)*Hsq(ul,uh,wl,wh,F(3,2),F(3,2),-1)/(g*g*g)
 if name=='opposite_pulse':return Hsq(ul,uh,wl,wh,F(1),F(1),-1)/(g*g*g)
 raise ArithmeticError(name)

root=Path(__file__).resolve().parent;result={'scope':'Exact predicates on complex rectangle only; contour phase rate separate','field_rectangle':{'Re':['9/20','1/2'],'Im_squared':['0','1089/10000']},'product_factors':J,'fixed_grid_scale':str(S),'derivative_cells':der,'tasks':{}}
start=time.time()
for name in tasks:
 leaves=[];todo=[([F(0),F(1),F(0),F(1),F(0),F(1)],'')];nodes=0;maxu=F(0)
 while todo:
  ends,path=todo.pop();nodes+=1
  try:r=bound(name,ends);upper=F(r.hi,S)
  except ArithmeticError:upper=F(10**6)
  if upper<tasks[name][2]:
   maxu=max(maxu,upper);leaves.append({'path':path,'upper':str(upper)});continue
  need(len(path)<42,'depth limit '+name+' '+path+' '+str(upper))
  dimensions=[0,1] if tasks[name][0]==tasks[name][1]else[0,1,2]
  dim=max(dimensions,key=lambda j:ends[2*j+1]-ends[2*j]);mid=(ends[2*dim]+ends[2*dim+1])/2
  left=ends.copy();right=ends.copy();left[2*dim+1]=mid;right[2*dim]=mid
  todo.append((right,path+str(dim)+'R'));todo.append((left,path+str(dim)+'L'))
 result['tasks'][name]={'leaves':leaves,'node_count':nodes,'max_squared_upper':str(maxu),'target':str(tasks[name][2])}
 print(name,'passed',len(leaves),'cells, max',float(maxu),'seconds',round(time.time()-start,1),flush=True)
 (root/'complex_corridor_certificate.json').write_text(json.dumps(result,indent=2)+'\n')
result['all_checks_passed']=True
(root/'complex_corridor_certificate.json').write_text(json.dumps(result,indent=2)+'\n')
