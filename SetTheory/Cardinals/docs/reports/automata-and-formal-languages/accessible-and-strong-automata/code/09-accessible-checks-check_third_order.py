"""Independent order-three check of the two-boundary algorithm."""
import json, math
from pathlib import Path
import sympy as s
import mpmath as mp
mp.mp.dps=70
P=Path(__file__).resolve().parent
old=json.loads((P/'verification.json').read_text())
k,v,z,u,r=s.symbols('k v z u r', positive=True)
D=lambda f:s.expand(z*(s.diff(f,z)-u*s.diff(f,u)))
C=[z/(1-u)]
for j in range(5):C.append(D(C[-1]))
C=[s.factor(x.subs({z:k*v,u:1-v})) for x in C]
Cf=[s.lambdify((k,v),x,'mpmath') for x in C]
# Generic Gaussian-moment coefficient p2, using an unstandardized x with variance 1/K2.
x,K2,K3,K4,K5,K6=s.symbols('x K2 K3 K4 K5 K6',positive=True)
E1=-s.I*(x+K3*x**3/6);E2=K4*x**4/24;E3=s.I*K5*x**5/120;E4=-K6*x**6/720
G=lambda p:s.expand(sum(coeff*(s.factorial2(j-1) if j else 1)/K2**(j//2) for (j,),coeff in s.Poly(s.expand(p),x).terms() if j%2==0))
p1=G(E2+E1**2/2)
p2=G(E4+E1*E3+E2**2/2+E1**2*E2/2+E1**4/24)
f1=s.lambdify((K2,K3,K4),p1,'mpmath');f2=s.lambdify((K2,K3,K4,K5,K6),p2,'mpmath')
out={}
for kk in [2,3,4]:
 vv=mp.mpf(old['large_n'][str(kk)]['c']) # overwritten intentionally below
 vv=1+mp.lambertw(-kk*mp.exp(-kk))/kk;om=1-vv;cc=1-kk*om;alpha=kk-1
 cums=[f(kk,vv) for f in Cf]
 pp1=f1(*cums[1:4]);pp2=f2(*cums[1:6])
 F1=mp.mpf(13)/(12*kk)-mp.mpf(1)/12;F2=F1**2/2-mp.mpf(1)/(2*kk**2)
 tau1=F1+pp1;tau2=F2+F1*pp1+pp2
 d1=mp.mpf(old['large_n'][str(kk)]['d1']);d2=mp.mpf(old['large_n'][str(kk)]['d2'])
 q=om*vv**alpha
 accum=mp.mpf(0)
 for rr in range(1,600):
  w=mp.binomial(kk*rr,rr)*q**rr
  R1=-mp.mpf(alpha)*rr**2/2
  R2=mp.mpf(alpha)*rr**2*(alpha*rr-1)*(3*rr+1)/24
  R3=-mp.mpf(alpha*rr)*(alpha*rr-1)*(alpha*rr-2)*rr**2*(rr+1)/48
  L1=mp.mpf(alpha)*rr**2/2-mp.mpf(rr)/2
  L2=mp.mpf(alpha)*rr**3/6-mp.mpf(rr**2)/4+tau1*rr
  L3=mp.mpf(alpha)*rr**4/12-mp.mpf(rr**3)/6+tau1*rr**2+(2*tau2-tau1**2)*rr
  W2=R2+R1*L1+L2+L1**2/2
  W3=R3+R2*L1+R1*(L2+L1**2/2)+L3+L1*L2+L1**3/6
  accum+=w*(cc*W3+d1*(W2+mp.mpf(rr**2)/2)+mp.mpf('1.5')*d2*rr)
 forcing=mp.mpf(0)
 if kk==2:forcing=vv**2*(-mp.mpf('.5')+cums[2]/cums[1]**2)+12*vv**3
 if kk==3:forcing=vv**3
 d3=-cc*(accum+forcing)
 rows=[]
 for row in old['large_n'][str(kk)]['rows']:
  n=row['n'];scaled3=mp.mpf(row['n3_after_d2'])
  rows.append({'n':n,'n3_after_d2':str(scaled3),'n4_after_d3':str(n*(scaled3-d3))})
 out[kk]={'tau1':str(tau1),'tau2':str(tau2),'small_boundary_order3':str(forcing),'d3':str(d3),'rows':rows}
 print(kk,'d3=',mp.nstr(d3,35),'n500=',rows[-1])
(P/'third_order.json').write_text(json.dumps(out,indent=2)+'\n')
