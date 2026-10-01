from math import comb,isqrt,gcd
from fractions import Fraction
from pathlib import Path
import json
ROOT=Path(__file__).parent

def taildata(a,b,N,M):
 A=[comb(N,b-i)for i in range(3)];B=[comb(M,a-i)for i in range(3)]
 C0=A[0]*B[0];C1=A[1]*B[1];C2=A[2]*B[2]
 D1=a*A[0]*B[1]+b*A[1]*B[0]
 D2=a*A[1]*B[2]+b*A[2]*B[1]
 E2=comb(a,2)*A[0]*B[2]+a*b*A[1]*B[1]+comb(b,2)*A[2]*B[0]
 return A,B,C0,C1,C2,D1,D2,E2

def gadget(a,b,N,M,W):
 r=a+b;K=N*(W-1);R=r+K
 A,B,C0,C1,C2,D1,D2,E2=taildata(a,b,N,M)
 b1=C1*W+D1;b2=C2*W*W+D2*W+E2
 Lbar=W*(K-N+b)+(N-b)
 Sbar=W*W*(K-N+b)+(N-b)
 al=W*W*((R-1)*b1*b1-2*R*C0*b2)
 be=2*C0*W*(-b1*Lbar+R*(W-1)*(C1*W+b*A[1]*B[0]))
 ga=C0*C0*(R*Sbar-Lbar*Lbar)
 if al>=0:return None
 assert ga>0
 T=1+(be+isqrt(be*be-4*al*ga))//(-2*al)
 val=lambda t:al*t*t+be*t+ga
 assert val(T)<0 and val(T-1)>=0
 gg=gcd(gcd(abs(al),abs(be)),ga)
 return {'a':a,'b':b,'N':N,'M':M,'W':W,'K':K,'rank':R,'T':T,
  'vertices':r+N+M+2*K,'edges':a*b+a*M+b*N+2*K,
  'endpoint_quadratic_primitive':[al//gg,be//gg,ga//gg],
  'endpoint_quadratic_value_primitive':val(T)//gg,
  'prior_endpoint_quadratic_value_primitive':val(T-1)//gg,
  'factor':'W^(2N-2)*T^(2K-2)*gcd(alpha,beta,gamma)',
  'quadratic_gcd':gg}

