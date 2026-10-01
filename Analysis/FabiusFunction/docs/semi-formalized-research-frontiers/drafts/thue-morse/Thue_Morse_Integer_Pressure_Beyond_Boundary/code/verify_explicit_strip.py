"""Exact rational side conditions for the uniform-strip proof."""
from fractions import Fraction as Q
from math import factorial
import json
from pathlib import Path
checks={}
checks['saddle_upper']=Q(1,2)+sum(Q(3,2**(j+1)+3) for j in range(2,6))>Q(33,32)
checks['main_scale']=1+Q(47,30)+Q(19,30)*Q(4,5)+Q(1,15)*Q(4,5)**2>3
checks['tail_log_margin']=Q(93,1600)+Q(1,40)<Q(19,225)
checks['nearest_log_margin']=Q(26,1600)+Q(1,2)<1
checks['restoration_log_margin']=Q(43,1600)+Q(1,4)<Q(10,21)
checks['pressure_log_margin']=Q(31,1600)<Q(10,21)
for x,y in [(3,12),(4,24),(5,60),(8,1600)]:
 checks[f'exp_{x}_exceeds_{y}']=sum(Q(x)**k/factorial(k)for k in range(25))>y
# e<3: terms k>=2 are at most 1/2^(k-1), with strict inequality for k>=3.
checks['q_range']=Q(1,800)<Q(1,32)
checks['tiny_errors']=Q(1600,40)>3 # e^3>12>8
checks['log_strip_remote']=Q(7,4096)+Q(12,400)+Q(22,3200)-Q(19,225)<-Q(1,40)
checks['log_strip_nearest']=Q(17,8192)+Q(1,200)+Q(1,1600)-1<-Q(1,2)
checks['log_strip_restore']=Q(73,8192)+Q(1,200)+Q(1,1600)-Q(10,21)<-Q(1,4)
checks['log_strip_pressure']=Q(19,8192)+Q(1,200)+Q(3,1600)-Q(10,21)<0
checks['log12_below_five_halves']=sum(Q(5,2)**k/factorial(k)for k in range(25))>12
checks['log4096_above_eight']=sum(Q(1,factorial(k))for k in range(5))+Q(1,100)<Q(11,4) and Q(11,4)**8<4096
checks['log4096_below_nine']=sum(Q(3)**k/factorial(k)for k in range(5))>16
# For (A+B log d)/d, the scaled derivative is B-A-B log d<0 when A,B>0 and log d>1.
# For (A+B log d)/sqrt(d), it is B-A/2-(B/2)log d; each pair below is nonpositive already at log d=1.
checks['sqrt_scaled_derivative_signs']=all(B-Q(A,2)-Q(B,2)<=0 for A,B in [(22,8),(2,2),(6,2)])
checks['log_endpoint_domain']=1600>3 and 4096>3
assert all(checks.values())
(Path(__file__).resolve().parents[1]/'data'/'explicit_strip_checks.json').write_text(json.dumps({'all_checks_passed':True,'checks':checks,'scope':'Rational side conditions; the analytic inequalities are proved in explicit_strip_proof.md'},indent=2)+'\n')
print('All',len(checks),'exact side conditions pass')
