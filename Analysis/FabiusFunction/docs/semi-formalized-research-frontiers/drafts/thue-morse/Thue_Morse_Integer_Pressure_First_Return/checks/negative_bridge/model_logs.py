"""Rational model-crossing certificate; the article proves the pressure identification."""
from fractions import Fraction as F
from pathlib import Path
import json,sys
sys.path.insert(0,str(Path(__file__).parent))
from model_intervals import values,trig_rad,I,iv,S,require

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
