#!/usr/bin/env python3
"""Finite regressions and negative controls, not a universal proof substitute.
No builder import, no upstream code execution, and no floating point.
"""
import json, math
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def norm(t,a,b,c):
 q=t*t+c-a-b
 return (q*q+4*t*t*c-4*a*b)**2-16*t*t*c*q*q

def main():
 checks={}
 count=0
 for B in (8,16,32,64,128):
  for h in range(-B//4+1,B//4):
   for incoming in (-1,0):
    for target in (0,1):
     out,digit=divmod(2*h+target+incoming,B)
     assert out in (-1,0)
     if target:assert (digit in (0,1))==(h==0)
     count+=1
 checks['signed_borrow_exhaustive_cases']=count
 count=0;actual_binomial=0;missing_range_counterexample=None
 for N in (2,4,8,16,32,64):
  u=N.bit_length()-1
  for S in range(N):
   for T in range(N):
    X=N*N+(S+T)*N+(N-1-S);threshold=u+T.bit_count()+1
    if S+T<N:
     defect=S.bit_count()+T.bit_count()-(S+T).bit_count()
     assert X.bit_count()==threshold-defect
     assert (X.bit_count()>=threshold)==((S&T)==0)
     if N<=8:
      C=math.comb(2*X,X);v=(C&-C).bit_length()-1
      assert v==X.bit_count();actual_binomial+=1
     count+=1
    elif X.bit_count()!=threshold-(S.bit_count()+T.bit_count()-(S+T).bit_count()) and missing_range_counterexample is None:
     missing_range_counterexample={'N':N,'S':S,'T':T,'X':X,'valuation':X.bit_count(),'threshold':threshold}
 assert missing_range_counterexample is not None
 checks['popcount_exhaustive_cases']=count;checks['actual_binomial_valuations']=actual_binomial
 checks['negative_control_range_needed_for_identity']=missing_range_counterexample
 # The equal-weight norm is not a universal square detector.
 assert norm(2,4,16*2,16*2)==0 and math.isqrt(2)**2!=2
 checks['negative_control_unconditional_equal_weights']={'b':4,'r0':4,'r1':2,'r2':2,'rational_signed_sum':2,'norm_zero':True}
 count=0
 for cap in range(2,10):
  for g in range(-3,2*cap+3):
   for K in range(-4,5):
    for L in (-4,-3,-2,2,3,4):
     for offset in range(-3,4):
      C=K*L+offset
      delta=8*cap**3*g*K*K-g*g*(32*(C-K*L)**2*cap**3+g*g*K*K)
      if delta>0:
       assert K and 0<g<2*cap and 4*g*(C-K*L)**2<K*K and abs(C)>abs(K)
       count+=1
 checks['positive_delta_bootstrap_cases']=count
 count=0
 for U in (-8,-6,-4,4,6,8):
  for V in range(-20,21,4):
   A=U*(V+1);Pn=U*U*V
   assert abs(A)>=4 and abs(Pn)<=A*A
   for C in (-7,-5,-3,3,5,7):
    for K in range(-abs(C)+1,abs(C)):
     if not K:continue
     r1=(Pn*Pn-4)*K*K+4
     for xi in (-2,-1,1,2):
      D=(A*A-4)*C*C+4;E=C*C*D*xi;F=4*(A*A-4)*E*E+1;G=2*(A+2)*(A-2)**2*E*E-1
      for H in (-2,0,3):
       I=(G*G-1)*H*H+1;r2=D*F*I
       assert G%2==1 and I>=1 and r1<A**4*C*C+4<r2
       count+=1
 checks['strict_radical_separation_cases']=count
 checks['status']='PASS';(ROOT/'LOCAL_LEMMA_CHECKS.json').write_text(json.dumps(checks,indent=2)+'\n');print(json.dumps(checks,indent=2))
if __name__=='__main__':main()
