"""Rational model-crossing certificate; the article proves the pressure identification."""
from fractions import Fraction as F
from pathlib import Path
import json,sys
sys.path.insert(0,str(Path(__file__).parent))
from verify_eventual_66 import values,trig_rad,I,iv,S,require

def log_series(x):
 x=iv(x);k=0
 while x.lo<S:x=x*2;k-=1
 while x.lo>=2*S:x=x/2;k+=1
 z=(x-1)/(x+1);zz=z.square();term=z;v=iv(0)
 for j in range(80):v=v+term/(2*j+1);term=term*zz
 den=(1-zz)*161;rem=abs(term.hi)*2*S//den.lo+2
 ans=v*2;ans=I(ans.lo-rem,ans.hi+rem)
 if k:ans=ans+k*log2
 return ans
# Direct atanh series at z=1/3 to avoid recursive rescaling of log2.
z=iv(F(1,3));zz=z.square();term=z;v=iv(0)
for j in range(80):v=v+term/(2*j+1);term=term*zz
rem=abs(term.hi)*2*S//((1-zz)*161).lo+2
log2=I((v*2).lo-rem,(v*2).hi+rem)

def full_values(t):
 mu,g=values(t);a=trig_rad(t,True)/trig_rad(t,False)
 upper=g/(1-a*F(1,2**31))
 return mu,I(g.lo,upper.hi)

rows=[]
cases=[(F(3331483,10**6),[780030967,348301023]),(F(3331484,10**6),[780031119,348301241])]
for sigma,proposals in cases:
 phis=[];brackets=[]
 for k,numerator in enumerate(proposals,1):
  l=F(numerator,10**9);u=l+F(3,10**9)
  ml,gl=full_values(l);mu,gu=full_values(u)
  require(F(ml.hi,S)<sigma/k<F(mu.lo,S),"model saddle bracket")
  gi=I(gl.lo,gu.hi);ti=I(iv(l).lo,iv(u).hi)
  phi=k*log_series(gi)-iv(sigma)*log_series(ti)
  phis.append(phi);brackets.append(dict(k=k,lower=str(l),upper=str(u)))
 diff=phis[1]-phis[0]
 require(diff.hi<0 if sigma==F(3331483,10**6)else diff.lo>0,"model crossing sign")
 rows.append(dict(sigma=str(sigma),saddles=brackets,Phi2_minus_Phi1_lower=str(F(diff.lo,S)),Phi2_minus_Phi1_upper=str(F(diff.hi,S))))
out=dict(all_checks_passed=True,model_only=True,rows=rows)
out['pressure_slope_interval']=[str(2*F(3331483,10**6)),str(2*F(3331484,10**6))]
require(2*F(3331484,10**6)<F(20,3),"strictly below20/3")
Path(__file__).with_name('model_crossing_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print('Unique model crossing slope is between',*out['pressure_slope_interval'],'strictly below20/3. This checker certifies the model crossing; pressure identification is proved separately in the article.')
