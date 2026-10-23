"""Exact independent audit of signed Pell index reflection."""
import json,math
from pathlib import Path

def pell(A,n):
 x,y=1,0
 for _ in range(n): x,y=A*x+(A*A-1)*y,x+A*y
 return x,y
count=0
for A in range(2,10):
 for t in range(2,21):
    modulus=pell(A,t)[0]
    period=4*t
    seq=[pell(A,n)[1]%modulus for n in range(period+1)]
    assert seq[-1]==0 and pell(A,period)[0]%modulus==1
    for n in range(period+1):
        assert seq[period-n]==(-seq[n])%modulus
        count+=1
# Search signed-H hypotheses independently in a finite box.
cases=0; hits=0
for A in range(2,6):
 for B in range(2,8):
  for C in range(B,25):
   if not (2*B<=C or B%2):continue
   for J in range(1,4):
    for i in [-2,-1,1,2]:
     D=(A*A-1)*C*C+1;E=i*J*D*C*C;F=(A*A-1)*E*E+1
     G=A+F*(C*D+1-A)
     for j in range(-20,21):
      H=B+j*C;I=(G*G-1)*H*H+1;value=D*F*I
      cases+=1
      if (H-C)%F==0 and math.isqrt(value)**2==value:
       hits+=1;assert C==pell(A,B)[1]
result={'reflection_equalities':count,'signed_product_pell_assignments':cases,
'admissible_hits':hits,'warning':'Finite audits supplement the universal matrix proof; sparse admissible box is not an existence test.'}
Path(__file__).with_name('SIGNED_H_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
