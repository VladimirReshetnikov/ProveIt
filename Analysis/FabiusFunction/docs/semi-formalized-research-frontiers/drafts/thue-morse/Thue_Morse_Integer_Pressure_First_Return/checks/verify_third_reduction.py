"""Exact side conditions for the third-contour reduction, not its unresolved remainder."""
from fractions import Fraction as F
from pathlib import Path
import json
from model_intervals import values,iv,I,PI,S,bs,require
from model_logs import full_values,log_series

def atan_bounds(a,n=40):
 s=sum(((-1)**j*a**(2*j+1)/F(2*j+1) for j in range(n)),F(0))
 v=s+(-1)**n*a**(2*n+1)/F(2*n+1)
 return min(s,v),max(s,v)

d=256
checks={
 'eigen_map_inside_tenth':161*d*F(7,10)**d<F(1,10),
 'eigen_map_derivative':1600*d*F(7,10)**d<F(1,2),
 'canonical_tail_ratio':2000*d*F(7,10)**d<F(1,2),
 'all_d_continuation':F(7,10)*F(d+1,d)<1,
 'external_delta_bound':F(161,2000)<F(1,10),
 'external_contraction':F(1600,2000)<1,
 'external_log_bound':F(161,1839)<F(1,10),
}
a0,a1=F(45,100),F(46,100)
tl,tu=atan_bounds(a0);ml,mu=values(tu)
checks['third_lower_saddle']=F(ml.hi,S)<F(555,300)
tl1,tu1=atan_bounds(a1);ml1,mu1=values(tl1)
checks['third_upper_saddle']=F(ml1.lo,S)>F(559,300)
prod=iv(2)/PI
for b in bs:prod=prod*(1+a0*b)
checks['L_point_lower']=F(prod.lo,S)>F(13,10)
rho4=a1*F(7,5)**4/F(13,10)**3
checks['fourth_tail_gap']=rho4<F(81,100)
checks['third_model_base_exceeds_nine']=(a0*F(13,10))**3/a1**5>9
require(all(checks.values()),'eigen or third-window side condition')
rows=[]
for sigma,proposals in [(F(555,100),[682144536,423549203]),(F(559,100),[686203832,428603118])]:
 ps=[];brackets=[]
 for k,n in zip([2,3],proposals):
  l=F(n,10**9);u=l+F(4,10**9)
  ml,gl=full_values(l);mu,gu=full_values(u)
  require(F(ml.hi,S)<sigma/k<F(mu.lo,S),'model saddle bracket')
  val=k*log_series(I(gl.lo,gu.hi))-iv(sigma)*log_series(I(iv(l).lo,iv(u).hi))
  ps.append(val);brackets.append([k,str(l),str(u)])
 diff=ps[1]-ps[0]
 require(diff.hi<0 if sigma==F(555,100)else diff.lo>0,'second-third model crossing')
 rows.append({'sigma':str(sigma),'saddles':brackets,'Phi3_minus_Phi2':[str(F(diff.lo,S)),str(F(diff.hi,S))]})
out={'scope':'Exact eigen continuation and higher-cluster reduction only; lower-cluster remainder unresolved','all_checks_passed':True,'checks':checks,'rho4_upper':str(rho4),'model_crossing_rows':rows}
Path(__file__).with_name('third_reduction_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
