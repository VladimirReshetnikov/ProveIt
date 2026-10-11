"""Repeated-pole finite-part quadrature independent of collision counterterms."""
from pathlib import Path
import mpmath as mp
import json
mp.mp.dps=70

def f(r,x):return -mp.polygamma(r,x)
def conv(a,b):
 c=[mp.mpf(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c

def interval(rs,etas,r0,length):
 n=r0+1;kap=(-1)**r0*mp.factorial(r0);K=n+5
 jets=[mp.mpf(1)]
 for r,a in zip(rs,etas):jets=conv(jets,[f(r+j,a)/mp.factorial(j) for j in range(K+1)])[:K+1]
 small=min([length]+etas)*mp.mpf('1e-12')
 def regular(t):
  smooth=mp.fprod(f(r,a+t) for r,a in zip(rs,etas))
  if abs(t)<small:
   quot=mp.fsum(jets[j]*t**(j-n) for j in range(n,len(jets)))
  else:
   quot=(smooth-mp.fsum(jets[j]*t**j for j in range(n)))/t**n
  return kap*quot+f(r0,1+t)*smooth
 pts={mp.mpf(0),length/16,length/4,length/2,length}
 for a in etas:
  for p in [1,4,16]:
   if 0<a*p<length:pts.add(a*p)
 lower=kap*mp.fsum(jets[j]*length**(j-n+1)/(j-n+1) if j!=n-1 else jets[j]*mp.log(length) for j in range(n))
 return mp.quad(regular,sorted(pts))+lower

def separated(rs,shifts):
 points=sorted([(mp.frac(-a),i) for i,a in enumerate(shifts)]);ans=0
 for j,(pt,idx) in enumerate(points):
  end=points[j+1][0] if j+1<len(points) else points[0][0]+1
  oth=[k for k in range(len(rs)) if k!=idx]
  ans+=interval([rs[k] for k in oth],[mp.frac(pt+shifts[k]) for k in oth],rs[idx],end-pt)
 return ans

def counter(rs,a):
 d=len(rs);ans=mp.mpf(0)
 for m in range(d):
  for i in range(m+1,d):
   def other(x):
    ans=(-1)**rs[m]*mp.factorial(rs[m])/(x+a[m])**(rs[m]+1)
    ans*=mp.fprod(f(rs[k],1+x+a[k]) for k in range(m))
    ans*=mp.fprod(f(rs[k],x+a[k]) for k in range(m+1,d) if k!=i)
    return ans
   ni=rs[i]+1;kapi=(-1)**rs[i]*mp.factorial(rs[i])
   for p in range(1,ni+1):
    B=kapi*mp.diff(other,-a[i],ni-p)/mp.factorial(ni-p)
    if p==1:ans-=B*mp.log(a[i]-a[m])
    else:ans+=B/(p-1)/(a[i]-a[m])**(p-1)
 return ans

if __name__=='__main__':
 rows=[];q=2*mp.euler*mp.zeta(2)-mp.zeta(3)
 for power in [2,3]:
  e=mp.mpf(10)**(-power);a=[mp.mpf(0),e,2*e];rs=[0,1,0]
  original=separated(rs,a);c=counter(rs,a);res=original-c-q
  print(power,mp.nstr(original,35),mp.nstr(c,35),mp.nstr(res,35),flush=True)
  rows.append({'epsilon':str(e),'separated_fp':mp.nstr(original,50),'counterterm':mp.nstr(c,50),'residual':mp.nstr(res,40)})
 (Path(__file__).resolve().parents[1]/'results'/'polygamma_collision_checks.json').write_text(json.dumps({'precision':70,'indices':[0,1,0],'merged_moment':mp.nstr(q,50),'predicted_finite_anomaly':mp.nstr(mp.zeta(3)*(1-mp.log(2)),50),'rows':rows,'note':'Independent local Taylor subtraction; floating-point diagnostics, not interval certificates.'},indent=2)+'\n')
