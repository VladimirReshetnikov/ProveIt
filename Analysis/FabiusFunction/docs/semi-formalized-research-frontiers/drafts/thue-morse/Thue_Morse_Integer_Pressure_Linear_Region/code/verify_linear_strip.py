"""Exact arithmetic side conditions for the linear-strip theorem."""
from fractions import Fraction as Q
from math import factorial
from pathlib import Path
import json
checks={}
checks['small_branch']=Q(8,15)+Q(9,16)*4*Q(45,128)**3<Q(3,4)
checks['small_branch_geometric_ratio']=Q(5,4)*Q(45,128)<1
checks['interior_branch_gap']=Q(63,2048)/Q(9,8)==Q(7,256)>Q(1,40)
checks['large_gap']=Q(55,128)/Q(9,8)>Q(1,40)
checks['interior_contraction']=4*Q(39,40)**128<Q(3,4)
checks['pair_endpoint']=Q(39)*128**2/127<18**3
checks['exp_three_exceeds_eighteen']=sum(Q(3)**k/factorial(k)for k in range(6))>18
checks['remote_log']=Q(19,8192)+Q(9,128)-Q(19,225)<-Q(1,100)
checks['nearest_log']=Q(17,8192)+Q(8,128)-1<-Q(1,2)
L=Q(153,128);M=Q(1377,1024);A=Q(23409,16384)
checks['analytic_bases']=L==Q(17,16)*Q(9,8) and M==L*Q(9,8) and A==L*L and M<A
checks['restore_base']=A*Q(11,21)<Q(3,4)
checks['pressure_base']=A*Q(1024,1023)**2*Q(11,21)<Q(3,4)
checks['restoration_log']=Q(57,8192)-Q(29,128)<-Q(1,5)
checks['pressure_log']=Q(19,8192)-Q(113,512)<0
checks['complex_tan_disk']=Q(1,32)/(1-Q(1,32)**2)<Q(1,16)
checks['saddle_range']=Q(1,128)<Q(1,32)
checks['exponential_error_below_one_eighth']=Q(4096,100)>3
for x,y in [(5,132),(6,288),(4,24),(8,768)]:
 checks[f'exp_{x}_exceeds_{y}']=sum(Q(x)**j/factorial(j)for j in range(30))>y
checks['log_two_below_three_quarters']=sum(Q(3,4)**j/factorial(j)for j in range(5))>2
assert all(checks.values())
(Path(__file__).resolve().parents[1]/'data/linear_strip_checks.json').write_text(json.dumps({'all_checks_passed':True,'checks':checks},indent=2)+'\n')
print('All',len(checks),'linear-strip side conditions pass')
