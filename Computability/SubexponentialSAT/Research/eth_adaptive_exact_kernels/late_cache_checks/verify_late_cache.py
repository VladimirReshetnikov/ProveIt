#!/usr/bin/env python3
"""Original exact checker for a refined late CRT/tree schedule.
No archive code is imported. Arithmetic certificate, not full SAT engine.
"""
from fractions import Fraction as F
from math import isqrt,pi,log,sqrt
from pathlib import Path
import json
import sys

def require(c,m):
 if not c:raise ArithmeticError(m)
def sqrt_interval(x,S=10**15):
 q=isqrt(x.numerator*S*S//x.denominator)
 lo=F(q,S);hi=F(q+1,S)
 require(lo*lo<=x<hi*hi,'sqrt enclosure')
 return lo,hi
def atan_interval(q,n):
 # n even: last term negative, partial sum is lower bound.
 require(n%2==0,'atan parity')
 lo=sum(((-1)**j*F(1,(2*j+1)*q**(2*j+1)) for j in range(n)),F())
 return lo,lo+F(1,(2*n+1)*q**(2*n+1))
a,b=atan_interval(5,20);c,d=atan_interval(239,6)
piI=(16*a-4*d,16*b-4*c)
lnlo=2*sum((F(1,(2*j+1)*3**(2*j+1)) for j in range(20)),F())
lnhi=lnlo+F(2,41*3**41)*F(9,8)
R=(piI[0]/lnhi,piI[1]/lnlo)
require(R[0]>0,'positive log/pi')
x=F(833,50000);A=F(1,36);y=F(5003,540000)
require(x+y/(1-F(1,6))==A,'budget identity')
require(F(9,10)+6*x==F(24999,25000)<1,'root degree guard')
require(12**100<2**359,'tail exact log guard')
require(F(9,10)+F(359,100)/36==F(3599,3600)<1,'tail degree margin')
require((1+2*F(359,100))/36<1,'tail rounding')
require(A<F(9,10),'generated degree')
# eta>0 is equivalent to 6^3<5^4.
require(6**3<5**4,'positive tail taper growth')
# Normalized coefficient squares omit (pi/ln2)^2.
t0sq=F(7125,119);s0sq=F(46875,833)
k0sq=2/x;k1sq=F(2,16)/y
# a12/(1-1/sqrt6) < b12 =sqrt(12/25).
S6=sqrt_interval(F(6));a12=sqrt_interval(F(22,144));b12=sqrt_interval(F(12,25))
cachetail_hi=a12[1]/(1-1/S6[0])
require(cachetail_hi<b12[0],'tail root dominates all later cache levels')
# Second global candidate a8*K0 + b12*K1, in units pi/ln2.
childsq=F(14,64)*k0sq
follow_lo=sqrt_interval(childsq)[0]+sqrt_interval(F(12,25)*k1sq)[0]
follow_hi=sqrt_interval(childsq)[1]+sqrt_interval(F(12,25)*k1sq)[1]
troot=sqrt_interval(t0sq);sroot=sqrt_interval(s0sq)
require(follow_hi<troot[0],'root beats complete tail recursion')
stail=sqrt_interval(F(4,9)*k1sq)
require(stail[1]<sroot[0],'root memory dominance')
T=(R[0]*troot[0],R[1]*troot[1]);S=(R[0]*sroot[0],R[1]*sroot[1])
require(T[1]<F(35071,1000),'eventual 35.071 time')
require(S[1]<34,'eventual 34 space')
# Compare new and late supplied exact squared coefficients before common factor.
require(t0sq<F(24339,400),'time improves supplied 35.354588')
require(s0sq<F(915,16),'space improves supplied 34.274803')
out={'status':'PASS','scope':'Exact schedule/constant arithmetic, conditional on imported CRT/tree and source identities.',
 'root':{'r':8,'retained_fraction':str(x)},'tail':{'r':12,'first_retained_fraction':str(y),'ratio':'1/6','total_fraction':str(A)},
 'leaf_cutoff':'ceil(s/lambda^(3/4))','time_exact':'pi/ln(2)*sqrt(7125/119)','space_exact':'pi/ln(2)*sqrt(46875/833)',
 'time_display':pi/log(2)*sqrt(float(t0sq)),'space_display':pi/log(2)*sqrt(float(s0sq)),
 'full_descendant_candidate_display':pi/log(2)*float((follow_lo+follow_hi)/2),
 'tail_space_display':pi/log(2)*float(sum(stail)/2),
 'certified_time_interval':[str(v) for v in T],'certified_space_interval':[str(v) for v in S],
 'simple_eventual_time':'35.071','simple_eventual_space':'34',
 'root_power_margin':'1/25000','tail_row_power_margin_lower':'1/3600',
 'field_backend_exponent':'12/5','higher_memory':True,'all_comparisons_exact':True}
(Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('late_cache_checks.json')).write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if not k.startswith('certified_')},indent=2))
