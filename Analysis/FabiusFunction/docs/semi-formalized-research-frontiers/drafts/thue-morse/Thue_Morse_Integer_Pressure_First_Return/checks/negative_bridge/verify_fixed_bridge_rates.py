"""Exact full-phase endpoint certificates for a fixed contour and Phi_2.
Convexity in sigma extends the bounds to the entire sigma interval.
"""
from circle_tools import *
from model_logs import log_series
from pathlib import Path
import json,time
R=F(14,25);r=F(9,20);QMAX=F(1,5);CAP=F(199,200);TMIN=F(5371,10000)
Alog=5*log_series(iv(R/r))
need(Alog.lo>0,'positive logarithmic spiral slope')

def fieldbox(l,h):
 rr=r*exp_small(Alog*hull(l,h))
 co=I(cosp(h).lo,cosp(l).hi);si=I(sinp(l).lo,sinp(h).hi)
 return C(rr*co,rr*si)
LIPS=R*(Alog+PI)/(1-R*R)

def roundup(x):return F((x.numerator*S+x.denominator-1)//x.denominator,S)

def phase_upper(l,h,sigma,baseg,baset):
 a=fieldbox(l,h);gu=sqrt_interval(H2_box(a,F(1),R));m=(l+h)/2
 tc=atan_center(fieldbox(m,m));tcmod=sqrt_interval(tc.square_mod());lower=tcmod-LIPS*(h-l)/2
 if lower.lo<=0:return F(1000)
 p=sigma.denominator;n=sigma.numerator
 return roundup((fhi(gu)**3/flo(baseg)**2)**p*(baset/flo(lower))**n)
start=time.time();rows=[]
for sigma,tl,th in [(F(33,10),F(341384832,10**9),F(341384836,10**9)),(F(111,20),F(682144536,10**9),F(682144540,10**9))]:
 ml,gl=values(tl);mh,gh=values(th)
 need(2*ml.hi<iv(sigma).lo and 2*mh.lo>iv(sigma).hi,'endpoint second saddle bracket')
 p=sigma.denominator
 need(flo(gl)**(2*p)/th**sigma.numerator>5**p,'second-model rate exceeds five')
 todo=[(F(0),QMAX)];leaves=[];top=F(0)
 while todo:
  l,h=todo.pop();b=phase_upper(l,h,sigma,gl,th)
  if b<CAP**p:
   leaves.append([str(l),str(h),str(b)]);top=max(top,b);continue
  need(h-l>F(1,10**7),'phase subdivision guard')
  m=(l+h)/2;todo.extend([(l,m),(m,h)])
 # Outer |atan a| lower is inherited from the full exact outer56 certificate.
 gp=sqrt_interval(H2_box(C(iv(R),iv(0)),F(1),R))
 outer=roundup((fhi(gp)**2/flo(gl)**2)**p*(th/TMIN)**sigma.numerator)
 need(outer<CAP**p,'outer second-rate separation')
 rows.append({'sigma':str(sigma),'second_saddle':[str(tl),str(th)],'mean_left': [str(flo(ml)),str(fhi(ml))],'mean_right':[str(flo(mh)),str(fhi(mh))],'model_g_lower':str(flo(gl)),'exponent_power':p,'phase_leaves':leaves,'maximum_phase_ratio_power':str(top),'outer_ratio_power_upper':str(outer)})
 print('sigma',sigma,'cells',len(leaves),'phase max',float(top)**(1/p),'outer',float(outer)**(1/p),'elapsed',time.time()-start,flush=True)
out={'all_checks_exact':True,'all_checks_passed':True,'sigma_interval':['33/10','111/20'],'fixed_spiral_start':str(r),'fixed_spiral_end':str(R),'phase_over_pi':['0','1/5'],'rate_cap':str(CAP),'second_model_rate_lower':'5','atan_outer_lower':str(TMIN),'outer_atan_source':'../outer56/verify_outer56.json','rows':rows,'scope':'Full-phase endpoint bounds; convexity in sigma is proved in the companion note. No sign claim is made below the first model crossing.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print('ALL PASS',flush=True)
