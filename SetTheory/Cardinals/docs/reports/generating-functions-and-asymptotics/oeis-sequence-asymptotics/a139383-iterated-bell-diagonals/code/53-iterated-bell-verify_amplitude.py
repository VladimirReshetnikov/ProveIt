from mpmath import iv
from fractions import Fraction
import time,sys
iv.dps=30
# Every substantive operation below is outward-rounded interval arithmetic.
K=20
q=[Fraction(1)]
for n in range(1,K+2):q.append(-sum(Fraction((-2)**k,k+1)*q[n-k] for k in range(1,n+1)))
c=[iv.mpf(v.numerator)/v.denominator for v in q]
Q=int(sys.argv[1]) if len(sys.argv)>1 else 2048
M=64
S=iv.mpf(0); maxerr=iv.mpf(0); minx=100
start=time.time()
for j in range(Q):
 th=iv.pi*iv.mpf([j,j+1])/Q
 z=iv.exp(iv.j*th)/2
 # Remove roundoff undershoot at pi: exact arc is upper half plane.
 z=iv.mpc(z.real,iv.mpf([max(0,z.imag.a),z.imag.b]))
 u=z
 for k in range(12):
  arg=1+u
  # The whole input rectangle avoids the logarithmic singularity.
  assert arg.real.a>0 or arg.real.b<0 or arg.imag.a>0 or arg.imag.b<0
  assert arg.imag.a>=0
  u=iv.log(arg)
  assert u.imag.a>=0
 w=2/u
 for k in range(12,M):
  r=abs(w).a
  assert r>2
  t=1/w
  p=c[K+1]
  for n in range(K,1,-1):p=c[n]+t*p
  eps=iv.mpf(1)/3*(2/r)**K/(r-2)
  w=w+1+t*p+iv.mpc([-eps.b,eps.b],[-eps.b,eps.b])
 x=w.real.a
 assert x>=4
 V=w+iv.log(w)/3+1/(18*w)-M
 e=2/x**2
 f=iv.exp(V)
 error=abs(f)*(iv.exp(e)-1)
 val=(z*f).real+iv.mpf([-error.b/2,error.b/2])
 S+=val/Q
 minx=min(minx,float(x))
 if j%max(1,Q//8)==0:print(j,str(S),time.time()-start,flush=True)
print('RESULT',Q,S,'minx',minx,'time',time.time()-start)

if Q==2048:
 assert S.a>iv.mpf(214)/100
 assert S.b<iv.mpf(243)/100
 print('CERTIFIED: 214/100 < J < 243/100')
else:
 assert S.a>1
 print('CERTIFIED: J > 1')
