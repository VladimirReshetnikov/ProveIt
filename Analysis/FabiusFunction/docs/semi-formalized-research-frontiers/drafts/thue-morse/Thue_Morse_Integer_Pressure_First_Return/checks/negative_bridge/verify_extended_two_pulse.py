"""Exact two-pulse circle extension for all second saddles sigma in [3.3,5.59]."""
from circle_tools import *
from pathlib import Path
import json,time
TLO=F(17,50);THI=F(68621,100000);RLO=F(8,25);RHI=F(41,50);CAP=F(99,100)
need(iv(2*THI).hi<(PI/2).lo,'tangent sine monotonicity range')
# Exact coverage of all second saddles by monotonicity of the model mean.
need(2*values(TLO)[0].hi<iv(F(33,10)).lo,'lower t coverage')
need(2*values(THI)[0].lo>iv(F(559,100)).hi,'upper t coverage')
# atanh(RLO)<TLO proves |tan z|>=RLO on every retained circle.
s=sum((RLO**(2*j+1)/F(2*j+1)for j in range(40)),F(0));s+=RLO**81/(81*(1-RLO*RLO))
need(s<TLO,'lower annulus')
need((trig_rad(THI,True)/trig_rad(THI,False)).hi<iv(RHI).lo,'upper annulus')
need((sinp(F(1,32))/cosp(F(1,32))).hi<iv(F(1,10)).lo,'signed threshold')
need((sinp(F(17,64))/cosp(F(17,64))).hi<iv(F(6,5)).lo,'positive tangent upper')
need((sinp(F(1,8))/cosp(F(1,8))).lo>iv(F(2,5)).hi,'third factor lower')
need((sinp(F(1,16))/cosp(F(1,16))).lo>iv(F(19,100)).hi,'fourth factor lower')
need(RHI*F(6,5)<1,'positive angular contributions monotone')
pos=2*sum((RLO*b/(1+RLO*b)**2 for b in [F(1),F(2,5),F(19,100)]),F(0));neg=RLO*F(1,10)/(RLO-F(1,10))**2
need(pos-neg>F(1,100),'deep angular margin')

def upper(L,b):
 tl,th,ql,qh=b;a=tangent_box(tl,th,ql,qh);rr=a.square_mod();rr=I(max(iv(RLO*RLO).lo,rr.lo),min(iv(RHI*RHI).hi,rr.hi));top=F(0)
 for sign in [-1,1]:
  aa=C(sign*a.re,sign*a.im);p=iv(1)
  for j in range(1,L+1):
   c,s=cs(F(1),j);v=c.square()+rr*s.square()+2*aa.re*c*s;p=p*I(0,v.hi)
  val=p*H2_box(aa,1+F(1,2**L),RHI)/(glower(tl).square().square())
  top=max(top,fhi(val))
 return top
start=time.time();rows=[]
for L in [1,2,3]:
 todo=[(TLO,THI,F(0),F(1,2))];leaves=[];nodes=0;maxup=F(0)
 while todo:
  b=todo.pop();nodes+=1;v=upper(L,b)
  if v<CAP*CAP:
   leaves.append([*[str(x)for x in b],str(v)]);maxup=max(maxup,v);continue
  need(nodes<200000,'subdivision count')
  tl,th,ql,qh=b
  if (th-tl)/(THI-TLO)>2*(qh-ql):
   m=(tl+th)/2;todo.extend([(tl,m,ql,qh),(m,th,ql,qh)])
  else:
   m=(ql+qh)/2;todo.extend([(tl,th,ql,m),(tl,th,m,qh)])
 rows.append({'L':L,'nodes':nodes,'leaves':leaves,'maximum_squared_upper':str(maxup)});print('L',L,'leaves',len(leaves),'upper',float(maxup),'elapsed',time.time()-start,flush=True)
out={'all_checks_exact':True,'all_checks_passed':True,'sigma_range':['33/10','559/100'],'t_range':[str(TLO),str(THI)],'annulus':[str(RLO),str(RHI)],'deep_cutoff':4,'deep_angular_margin':'1/100','deep_positive_lower':str(pos),'deep_negative_upper':str(neg),'shallow_cap':str(CAP),'rows':rows}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print('ALL PASS',flush=True)
