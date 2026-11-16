#!/usr/bin/env python3
"""Exact standard-library congruence and Cartesian pullback checks at the axes.
No trigonometry, floating point, or external symbolic algebra is used.
"""
import json
from pathlib import Path
import verify_stdlib as k
k.N=6; k.ZERO_EXP=(0,)*6
pr,pu,pz,pa,pm,pq=[k.variable(i) for i in range(6)]
one={k.ZERO_EXP:1}
rho=k.padd(k.pmul(pu,pu),k.pmul(pz,pz))
ph=k.padd(one,rho)
pj=k.padd(one,k.pscale(rho,-1))
pSb=k.padd(k.pmul(k.pmul(pr,pr),k.pmul(ph,ph)),k.pmul(k.pmul(pa,pa),k.pmul(pj,pj)))
k.FACTORS=[{k.ZERO_EXP:2},ph,pSb,rho]; k.POWER_CACHE.clear()
def derivative(p,i):
 return k.pder(p,i-1) if i in (1,2,3) else {}
k.deriv_poly=derivative
# The BL engine deliberately differentiates only r and x. Here the two
# stereographic coordinates are both active, so explicitly extend that rule.
def stereographic_diff(self,i):
 k.COUNTS['differentiate'] += 1
 value=k.Rat(derivative(self.p,i),self.d)
 for j in (1,2,3):
  if self.d[j]:
   den=[0]*4; den[j]=1
   value=value-self*k.Rat(k.pscale(derivative(k.FACTORS[j],i),self.d[j]),tuple(den))
 return value
k.Rat.diff=stereographic_diff
r,u,z,a,m,q=[k.Rat(p) for p in (pr,pu,pz,pa,pm,pq)]
h=k.Rat(ph); ih=k.Rat(1,(0,1,0,0)); Sb=k.Rat(pSb)
S=Sb*ih**2; iS=h*h*k.Rat(1,(0,0,1,0))
half=k.Rat(1,(1,0,0,0)); quarter=half*half
L=2*m*r-q*q
eta=[k.Rat(0),k.Rat(0),-4*z*ih**2,4*u*ih**2]
e=[[k.Rat(int(i==j)) for j in range(4)] for i in range(4)]
p=[e[0][i]-a*eta[i] for i in range(4)]
c=(L-S)*half*iS
n=[e[1][i]-a*eta[i]+c*p[i] for i in range(4)]
g=[[ -e[0][i]*e[0][j]+e[0][i]*e[1][j]+e[1][i]*e[0][j]
     -a*(e[1][i]*eta[j]+eta[i]*e[1][j])
     +4*S*ih**2*(e[2][i]*e[2][j]+e[3][i]*e[3][j])
     +a*a*eta[i]*eta[j]+L*iS*p[i]*p[j]
     for j in range(4)] for i in range(4)]
gnull=[[p[i]*n[j]+n[i]*p[j]+4*S*ih**2*(e[2][i]*e[2][j]+e[3][i]*e[3][j]) for j in range(4)] for i in range(4)]
k.check('stereographic_null_congruence',(g[i][j]-gnull[i][j] for i in range(4) for j in range(4)))
C=[p,n,e[2],e[3]]
Ci=[[k.Rat(1),k.Rat(0),a*eta[2],a*eta[3]],[-c,k.Rat(1),a*eta[2],a*eta[3]],e[2],e[3]]
k.check('coframe_inverse',(sum(C[i][h0]*Ci[h0][j] for h0 in range(4))-int(i==j) for i in range(4) for j in range(4)))
J=k.matrix(); J[0][1]=J[1][0]=k.Rat(1)
J[2][2]=J[3][3]=h*h*quarter*iS
gi=k.mmul(k.mmul(Ci,J),k.transpose(Ci))
k.check('stereographic_metric_inverse',(sum(g[i][h0]*gi[h0][j] for h0 in range(4))-int(i==j) for i in range(4) for j in range(4)))
def determinant(M):
 ans=k.Rat(0)
 for p0 in k.permutations(range(4)):
  term=k.Rat((-1)**sum(p0[i]>p0[j] for i in range(4) for j in range(i+1,4)))
  for i in range(4): term=term*M[i][p0[i]]
  ans=ans+term
 return ans
k.check('stereographic_metric_determinant',[determinant(g)+16*S*S*ih**4])
# T=v-r: coordinate v is not a coefficient indeterminate, so supply its row.
cart=[None,2*(r*u-a*z)*ih,2*(r*z+a*u)*ih,r*k.Rat(pj)*ih]
Jac=[e[0][:]]; Jac[0][1]=k.Rat(-1)
Jac += [[cart[i].diff(j) for j in range(4)] for i in range(1,4)]
gflat=[[g[i][j]-L*iS*p[i]*p[j] for j in range(4)] for i in range(4)]
pull=[[sum((-1 if b==0 else 1)*Jac[b][i]*Jac[b][j] for b in range(4)) for j in range(4)] for i in range(4)]
k.check('cartesian_minkowski_pullback',(pull[i][j]-gflat[i][j] for i in range(4) for j in range(4)))
k.check('cartesian_jacobian',[determinant(Jac)-4*S*ih**2])
# p is null for both metrics; the check for the full metric also follows directly.
k.check('kerr_schild_covector_null',[sum(gi[i][j]*p[i]*p[j] for i in range(4) for j in range(4))])
res={'status':'PASS','engine':'Python standard library','variables':['r','u','z','a','m','q'],
 'domain':'Sigma>0; h=1+u^2+z^2>=1; includes both polar centers and Delta=0',
 'checks':k.CHECKS,'arithmetic_counters':k.COUNTS}
(Path(__file__).resolve().parents[1]/'certificates'/'stereographic_results.json').write_text(json.dumps(res,indent=2)+'\n')
k.announce('PASS: stereographic regularity and flat pullback')
