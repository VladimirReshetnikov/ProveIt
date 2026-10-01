"""Exact regression checks of slice reflection and strict TV in a two-coordinate model."""
from fractions import Fraction as F
from pathlib import Path
import json

def integral_power(lo,hi,p):return (hi**(p+1)-lo**(p+1))/F(p+1)
checks=0
for M in range(1,6):
 b=F(3,2);a=M*b
 for h in range(1,8*(M+1)):
  u=b*F(h,8)
  if not 0<u<a+b:continue
  lo=max(F(0),u-b);hi=min(a,u)
  for k in range(M):
   L=max(k*b,lo);U=min((k+1)*b,hi)
   if L<U:assert u+k*b-L==U and u+k*b-U==L
  for p in range(5):
   residue=sum(integral_power(max(k*b,lo)-k*b,min((k+1)*b,hi)-k*b,p)for k in range(M)if max(k*b,lo)<min((k+1)*b,hi))
   target=integral_power(u-hi,u-lo,p)
   assert residue==target,(M,u,p,residue,target)
   checks+=1
# Q: independent uniforms X in[0,2],Y in[0,1]; P: conditioning X+Y<=1.
# Likelihoods are ell_X=4(1-x)_+ and ell_Y=2(1-y).
def integ_linear(A,B,lo,hi):return A*(hi-lo)+B*(hi*hi-lo*lo)/2
TV_X=(integ_linear(3,-4,F(0),F(3,4))+integ_linear(-3,4,F(3,4),F(1))+F(1))/4
TV_Y=(integ_linear(1,-2,F(0),F(1,2))+integ_linear(-1,2,F(1,2),F(1)))/2
assert TV_X==F(9,16) and TV_Y==F(1,4) and TV_X-TV_Y==F(5,16)
out={'slice_moment_identities':checks,'orders_checked':[0,1,2,3,4],'integer_cap_ratios_checked':[1,2,3,4,5],'includes_internal_sum_breakpoints':True,'strict_TV_example':{'caps':[2,1],'beta':0,'weight':'indicator{s<=1}','TV_larger':'9/16','TV_smaller':'1/4','strict_difference':'5/16'},'all_checks_passed':True}
Path(__file__).with_name('slice_checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
