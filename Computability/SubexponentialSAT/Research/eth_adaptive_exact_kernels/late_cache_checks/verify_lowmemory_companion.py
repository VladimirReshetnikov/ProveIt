#!/usr/bin/env python3
"""Exact arithmetic check of the optional lower-memory CRT/tree companion."""
from fractions import Fraction as F
from math import isqrt,pi,log,sqrt
from pathlib import Path
import json
import sys

def require(c,m):
 if not c:raise ArithmeticError(m)
def si(x,S=10**15):
 q=isqrt(x.numerator*S*S//x.denominator);lo=F(q,S);hi=F(q+1,S)
 require(lo*lo<=x<hi*hi,'sqrt');return lo,hi
def plus(x,y):return x[0]+y[0],x[1]+y[1]
def mul(x,y):return x[0]*y[0],x[1]*y[1]
def atan(q,n):
 lo=sum(((-1)**j*F(1,(2*j+1)*q**(2*j+1)) for j in range(n)),F())
 return lo,lo+F(1,(2*n+1)*q**(2*n+1))
a,b=atan(5,20);c,d=atan(239,6)
L=2*sum((F(1,(2*j+1)*3**(2*j+1)) for j in range(20)),F())
U=L+F(2,41*3**41)*F(9,8);R=((16*a-4*d)/U,(16*b-4*c)/L)
def factors(r):
 q,rem=divmod(r,3);sizes=[q+(i<rem) for i in range(3)]
 def cost(v):return (sum(v)-F(21,25)*min(v))/r**2
 def merge(n):
  if n<=1:return F(0)
  a=n//2;b=n-a
  return max(cost([2*a*(r-n),2*a*b,2*b*(r-n)]),merge(a),merge(b))
 vs=[2*sizes[i]*sizes[j] for i in range(3) for j in range(i+1,3)]
 return F(2*(r-1),r*r),max(cost(vs),max(merge(v) for v in sizes)),F(max(2*v*(r-v) for v in sizes),r*r)
rs=[7,9,8,6,5,4,4]
xs=[F(v) for v in ['89/5000','13/1250','29/10000','1/500','1/500','1/500','1/500']]
A=F(0);m=F(1);P=(F(0),F(0));times=[];spaces=[];records=[]
for d,(r,x) in enumerate(zip(rs,xs)):
 A+=x;bound=F(1,10)/((2 if d==0 else 1)*A)
 require(r**bound.denominator<2**bound.numerator,'degree guard')
 a,b,j=factors(r);ksq=2*m*m/x
 local=si(b*ksq);times.append(plus(P,local));spaces.append(si(j*ksq))
 records.append({'depth':d,'r':r,'cache_square':str(a),'tree_work_square':str(b),'memory_square':str(j)})
 P=plus(P,si(a*ksq));m*=F(2,r)
require(m==F(1,1890),'tailmass');x7=F(239,40000)
require(A+x7/(1-F(3,4))==F(63,1000),'totalbudget')
require(3**63<2**100,'taildegreeguard')
a,b,j=factors(3);ksq=2*m*m/x7
sqrt3=si(F(3));gam=(F(4,3)/sqrt3[1],F(4,3)/sqrt3[0]);ai=si(a)
cachetail=(ai[0]/(1-gam[0]),ai[1]/(1-gam[1]))
require(cachetail[0]>si(b)[1],'tail cache limit dominates local work')
Tail=plus(P,mul(si(ksq),cachetail))
require(all(t[1]<Tail[0] for t in times),'tail dominates every prefix')
spaces.append(si(j*ksq));require(all(t[1]<spaces[0][0] for t in spaces[1:]),'rootmemory')
T=mul(R,Tail);S=mul(R,spaces[0]);require(T[1]<F(37325,1000),'time37.325');require(S[1]<F(33624,1000),'space33.624')
out={'status':'PASS','scope':'Optional lower-memory companion using the same late CRT/tree backend.',
 'time_display':float(sum(T)/2),'space_display':float(sum(S)/2),'eventual_time':'37.325','eventual_space':'33.624',
 'source_schedule':'cache_schedule_new.md root7/multi-depth schedule unchanged',
 'time_bottleneck':'limiting tail ancestor-cache sum','space_bottleneck':'root boundary table',
 'exact_time_interval':[str(v) for v in T],'exact_space_interval':[str(v) for v in S],'factor_ledger':records}
(Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('lowmemory_companion_checks.json')).write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if not k.startswith('exact_')},indent=2))
