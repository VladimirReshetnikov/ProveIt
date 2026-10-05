"""Exact bracket for the second/third positive-model rate crossing."""
from fractions import Fraction as F
from pathlib import Path
import json
from model_intervals import values,I,iv,S,require
from model_logs import full_values,log_series
rows=[]
for sigma,proposals in [(F(5572505,10**6),[684434187,426398869]),(F(5572507,10**6),[684434390,426399122])]:
 phis=[];brackets=[]
 for k,n in zip([2,3],proposals):
  l=F(n,10**9);u=l+F(4,10**9)
  ml,gl=full_values(l);mu,gu=full_values(u)
  require(F(ml.hi,S)<sigma/k<F(mu.lo,S),'model saddle bracket')
  z=k*log_series(I(gl.lo,gu.hi))-iv(sigma)*log_series(I(iv(l).lo,iv(u).hi))
  phis.append(z);brackets.append({'k':k,'lower':str(l),'upper':str(u)})
 diff=phis[1]-phis[0]
 require(diff.hi<0 if sigma==F(5572505,10**6)else diff.lo>0,'crossing sign')
 rows.append({'sigma':str(sigma),'saddles':brackets,'Phi3_minus_Phi2':[str(F(diff.lo,S)),str(F(diff.hi,S))]})
out={'all_checks_exact':True,'all_checks_passed':True,'sigma_crossing_interval':['5.572505','5.572507'],'degree_over_m_interval':['11.145010','11.145014'],'rows':rows,'scope':'Model crossing; connection to pressure is proved separately in final_contour_deduction.md'}
Path(__file__).with_name('second_model_crossing_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
