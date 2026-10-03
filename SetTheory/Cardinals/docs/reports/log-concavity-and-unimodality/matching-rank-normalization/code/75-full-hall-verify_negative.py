"""Exact replay of the finite counterexample construction for all large cores."""
from math import comb
from pathlib import Path
import json

def c(n,k):return comb(n,k) if 0<=k<=n else 0

def construct(a,b):
 r=a+b;K=(r-1)*a*b;H=(r+1)*a*b-2*r*(r-1)
 assert H>0
 h=1+(2*K+H-1)//H;n=b-1+h;m=a-1+h
 A=[c(n,b-i) for i in range(3)];B=[c(m,a-i) for i in range(3)]
 X=a*A[0]*B[1]+b*A[1]*B[0]
 Y=a*A[1]*B[2]+b*A[2]*B[1]
 Z=c(a,2)*A[0]*B[2]+a*b*A[1]*B[1]+c(b,2)*A[2]*B[0]
 alpha=(r-1)*A[1]**2*B[1]**2-2*r*A[0]*A[2]*B[0]*B[2]
 beta=2*(r-1)*A[1]*B[1]*X-2*r*A[0]*B[0]*Y
 gamma=(r-1)*X**2-2*r*A[0]*B[0]*Z
 assert alpha<0
 w=1+(abs(beta)+abs(gamma))//(-alpha)
 assert alpha*w*w+beta*w+gamma<0
 def coeff(k):
  return sum(c(a,i)*c(b,j)*c(n,k-i)*c(m,k-j)*w**(i+j)
    for i in range(a+1) for j in range(b+1) if i+j>=k)
 pr,pr1,pr2=coeff(r),coeff(r-1),coeff(r-2)
 assert pr==A[0]*B[0]*w**r
 assert pr1==A[1]*B[1]*w**r+X*w**(r-1)
 assert pr2==A[2]*B[2]*w**r+Y*w**(r-1)+Z*w**(r-2)
 gap=(r-1)*pr1**2-2*r*pr2*pr
 assert gap==w**(2*r-2)*(alpha*w*w+beta*w+gamma)<0
 return {'left_core':a,'right_core':b,'left_exterior':n,'right_exterior':m,'core_activity':w,'rank':r}
if __name__=='__main__':
 examples=[]
 for a in range(3,21):
  for b in range(3,21):
   rec=construct(a,b)
   if (a,b) in [(3,3),(3,4),(3,5),(4,4)]:examples.append(rec)
 out={'shape_pairs_checked':324,'core_range':[3,20],'all_top_coefficients_and_negative_gaps_verified':True,'examples':examples}
 Path(__file__).with_name('negative_verification.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps(out,indent=2))
