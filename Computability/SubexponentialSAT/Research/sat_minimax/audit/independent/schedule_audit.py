#!/usr/bin/env python3
from fractions import Fraction as F
from math import prod
import json
from decimal import Decimal as D, getcontext
getcontext().prec=80
class MP:
 @staticmethod
 def mpf(x):return D(x)
 @staticmethod
 def sqrt(x):return D(x).sqrt()
 @staticmethod
 def log(x):return D(x).ln()
 @staticmethod
 def nstr(x,digits):return format(x,"."+str(digits)+"g")
def atan(x):
 z=D(x);total=D(0);power=z;sign=1
 for i in range(200):
  total+=sign*power/D(2*i+1);power*=z*z;sign=-sign
 return total
mp=MP();mp.pi=16*atan(D(1)/5)-4*atan(D(1)/239)

def m(x):
 x=F(x);return mp.mpf(x.numerator)/x.denominator

def lt_log(A,r,b):
 # Certifies A log2(r) < b exactly, via integer powers.
 A,b=F(A),F(b)
 # clear denominators, reduce exponents with gcd
 from math import gcd
 x=A.numerator*b.denominator;y=b.numerator*A.denominator
 z=gcd(x,y);x//=z;y//=z
 return pow(r,x)<pow(2,y),x,y

def audit(optional=False):
 rs=[9,12,8,6,5,4,4,4]
 eta=list(map(F,['1577/100000','303/25000','17/3125','107/20000','219/50000','171/50000','43/20000','17/12500']))
 b2=list(map(F,['54113/169344','4110726305041430303/12559431766773663744','15/32','4/9','12/25','1/2','1/2','1/2']))
 if optional:
  rs[0]=10;eta[:2]=[F(301,20000),F(321,25000)]
  b2[:2]=[F(119061,387200),F(55241,185856)]
 tail_eta=F(30107,10000000);q=F(77,100);eps=F(1,100000)
 A=F(0);mu=F(1);kconst=mp.pi*mp.sqrt(2)/mp.log(2);paid=mp.mpf(0);times=[];spaces=[];checks=[]
 for d,(r,e,b) in enumerate(zip(rs,eta,b2)):
  prev=A;A+=e
  gates=[('inherited_degree',2*A if d==0 else A,F(1,10)),('fresh_side',2*A,1-prev),('rounding',2*A,1-A)]
  for name,aa,bb in gates:
   ok,x,y=lt_log(aa,r,bb)
   if not ok:raise AssertionError((d,name))
   checks.append({'depth':d,'gate':name,'r':r,'exponent_r':x,'exponent_2':y,'verified':True})
  K=kconst*m(mu)/mp.sqrt(m(e));alpha=mp.sqrt(2*(r-1))/r;beta=mp.sqrt(m(b))
  times.append(paid+(1+m(eps))*beta*K);spaces.append(beta*K);paid+=alpha*K;mu*=F(2,r)
 tail_A=A+tail_eta/(1-q)
 for name,aa,bb in [('inherited_degree',tail_A,F(1,10)),('fresh_side',2*tail_A,1-tail_A),('rounding',2*tail_A,1-tail_A)]:
  ok,x,y=lt_log(aa,3,bb)
  if not ok:raise AssertionError(('tail',name))
  checks.append({'depth':'tail_upper_envelope','gate':name,'r':3,'exponent_r':x,'exponent_2':y,'verified':True})
 K=kconst*m(mu)/mp.sqrt(m(tail_eta));gamma=m(F(2,3))/mp.sqrt(m(q));alpha=mp.mpf(2)/3;beta=mp.mpf(2)/3
 tail_time=paid+K*max((1+m(eps))*beta,alpha/(1-gamma))
 times.append(tail_time);spaces.append(beta*K)
 return {'kind':'optional_new_backend' if optional else 'conservative_backend','r_prefix':rs,'eta_prefix':list(map(str,eta)),
         'beta_squared_prefix':list(map(str,b2)),'eta_tail':str(tail_eta),'tail_ratio':str(q),
         'sum_eta':str(tail_A),'mu_tail':str(mu),'tail_work_ratio':mp.nstr(gamma,50),
         'time_by_depth':list(map(lambda x:mp.nstr(x,50),times)),
         'space_by_depth':list(map(lambda x:mp.nstr(x,50),spaces)),
         'maximum_time':mp.nstr(max(times),50),'maximum_time_depth':times.index(max(times)),
         'maximum_space':mp.nstr(max(spaces),50),'maximum_space_depth':spaces.index(max(spaces)),
         'exact_power_checks':checks,'numerical_scope':'Constants evaluated with 80-digit Decimal and 200-term Machin series; strict packing gates are exact integer comparisons.'}
if __name__=='__main__':
 out=[audit(),audit(True)]
 open(__import__('pathlib').Path(__file__).parent/'results'/'schedule_audit.json','w').write(json.dumps(out,indent=2)+'\n')
 for z in out:print({k:z[k] for k in ['kind','sum_eta','maximum_time','maximum_time_depth','maximum_space','maximum_space_depth']})
