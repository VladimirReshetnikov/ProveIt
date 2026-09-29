"""Non-proof numerical discovery; exact verifiers live in verify.py."""
from pathlib import Path
from fractions import Fraction as Q
import json, math, sys
import numpy as np
from scipy.optimize import root
import sympy as sp
from research import NAMES, TERMS, fmap, jac, defects, evalpoly, critical
BASE=Path(__file__).resolve().parent.parent

def upper(N, target):
 d=json.loads((BASE/'data/profiles.json').read_text()); counts=d['counts']
 P,D=defects(counts,N)
 estimates=json.loads((BASE/'data/critical_estimates.json').read_text())
 if len(estimates)>=N: guess=np.array(estimates[N-1][:17])
 else: guess=critical(counts,N,np.array(estimates[-1]))[:17]
 zeta=1/float(target)
 # Perturb every equation in the favorable direction to survive rounding.
 for eps in [1e-7,1e-8,1e-9,1e-10]:
  def fun(a):return np.array(fmap(zeta,a))-np.array([evalpoly(v,zeta) for v in D])-a+eps
  sol=root(fun,guess,tol=1e-11)
  for den in [10**9,10**10,10**12]:
   nums=[round(float(v)*den) for v in sol.x]; v=[Q(n,den) for n in nums]
   qz=1/Q(target); pref=[evalpoly(p,qz) for p in P]; defect=[evalpoly(p,qz) for p in D]
   res=[v[i]-fmap(qz,v)[i]+defect[i] for i in range(17)]
   if all(v[i]>=pref[i] for i in range(17)) and min(res)>0:
    cert={'N':N,'growth_upper':str(Q(target)),'zeta':str(qz),'denominator':den,'numerators':nums,'min_residual':str(min(res)),'g':str(v[4])}
    (BASE/f'data/upper_N{N}.json').write_text(json.dumps(cert,indent=2)+'\n')
    print('UPPER',N,target,'g',float(v[4]),'slack',float(min(res)),'den',den,'solver',sol.success)
    return cert
 raise RuntimeError('no certificate')

def dual(target='4.52349'):
 d=json.loads((BASE/'data/critical_estimates.json').read_text()); a=np.array(d[0][:17]);r=d[0][17]
 vals,vecs=np.linalg.eig(jac(r,a).T); index=np.argmin(abs(vals-1)); ell=vecs[:,index].real
 if min(ell)<0:ell=-ell
 assert min(ell)>0
 ell/=np.dot(ell,a)
 monomials=[]; beta=[]
 for i,row in enumerate(TERMS):
  for b,inds in row:
   x=r**b
   for j in inds:x*=a[j]
   beta.append(ell[i]*x);monomials.append((i,b,inds))
 M=len(monomials)
 B=sp.zeros(18,M)
 for k,(i,b,inds) in enumerate(monomials):
  B[i,k]-=1
  for j in inds:B[j,k]+=1
  B[17,k]=1
 rhs=sp.zeros(18,1);rhs[17]=1
 R,pivots=B.row_join(rhs).rref()
 assert all(p<M for p in pivots)
 free=[j for j in range(M) if j not in pivots]
 for den in [10**6,10**7,10**8,10**9]:
  rational=[None]*M
  for j in free:rational[j]=sp.Rational(round(beta[j]*den),den)
  for row,p in enumerate(pivots):rational[p]=R[row,M]-sum(R[row,j]*rational[j] for j in free)
  if min(rational)<=0:continue
  common=int(sp.ilcm(*[x.q for x in rational])); weights=[int(x*common) for x in rational]
  assert B*sp.Matrix(weights)==rhs*common
  sums=[sum(weights[k] for k,(i,_,_) in enumerate(monomials) if i==j) for j in range(17)]
  z=1/Q(target)
  score=sum(m*math.log(float(z**b*Q(sums[i],m))) for m,(i,b,inds) in zip(weights,monomials))
  if score>0:
   cert={'growth_lower':str(Q(target)),'zeta':str(z),'weights':weights,'row_sums':sums,'normalization':common,'discovery_log_product':score,'monomial_order':'Rows and terms in code/model.py, TERMS'}
   (BASE/'data/dual_original.json').write_text(json.dumps(cert,indent=2)+'\n')
   print('DUAL',target,'total',sum(weights),'minweight',min(weights),'terms',M,'logscore',score,'maxweight',max(weights))
   return cert
 raise RuntimeError('no dual certificate')

if __name__=='__main__':
 if len(sys.argv)>1:upper(int(sys.argv[1]),sys.argv[2])
 else:
  upper(16,'4.5039');dual()
