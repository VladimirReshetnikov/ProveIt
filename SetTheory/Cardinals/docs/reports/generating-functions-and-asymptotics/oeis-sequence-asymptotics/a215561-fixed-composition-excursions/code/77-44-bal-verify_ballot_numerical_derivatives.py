import mpmath as m,json
from itertools import product,combinations_with_replacement
from pathlib import Path
m.mp.dps=55
reports=[]
for q,ss,seeds in [(4,(-3,-1,1,3),[m.mpc('-.257','-.529'),m.mpc('-.257','.529')]),(5,(-2,-1,0,1,2),[(-3+m.sqrt(5))/2])]:
 h=q-2;zero=(m.mpf(0),)*h
 def critical(z):
  w=[m.exp(x) for x in z]+[m.mpf(1)]*2
  def P(u,k=0):return sum(wi*m.ff(s,k)*u**(s-k) for wi,s in zip(w,ss))
  tau=m.findroot(lambda u:P(u,1),(m.mpf('.99'),m.mpf('1.01')))
  lam=P(tau);roots=[m.findroot(lambda u:P(u)-lam,seed) for seed in seeds]
  E=(-1)**(-min(ss)+1)*lam*tau*m.fprod(roots)/w[0]
  V=tau*tau*P(tau,2)/lam
  return m.log(lam),m.log(E),-m.log(V)/2
 def deriv(which,indices):
  order=tuple(indices.count(i) for i in range(h))
  return m.diff(lambda *z:critical(z)[which],zero,order)
 H=m.matrix([[deriv(0,[i,j]) for j in range(h)] for i in range(h)]);G=H**-1
 g=[deriv(1,[i]) for i in range(h)];g2=m.matrix([[deriv(1,[i,j]) for j in range(h)] for i in range(h)])
 b=[deriv(2,[i]) for i in range(h)]
 kappa={}
 for inds in combinations_with_replacement(range(h),3):kappa[inds]=deriv(0,list(inds))
 amp=-sum(G[i,j]*(g2[i,j]+g[i]*g[j]+2*b[i]*g[j]) for i,j in product(range(h),repeat=2))/2
 amp+=sum(g[i]*kappa[tuple(sorted((j,k,l)))]*G[i,j]*G[k,l] for i,j,k,l in product(range(h),repeat=4))/2
 def P(u,k=0):return sum(m.ff(s,k)*u**(s-k) for s in ss)
 roots=[m.findroot(lambda u:P(u)-q,seed) for seed in seeds]
 alpha2=2*q/P(1,2);beta=-P(1,3)*alpha2/(6*P(1,2))
 d2=1+beta+q*sum(1/(r*P(r,1)) for r in roots)
 univ=-3*d2/2+alpha2/2
 full=(univ+amp)/q+(m.mpf(1)/q-q)/12
 phi=(1+m.sqrt(5))/2;r=phi-m.sqrt(phi)
 target=(-37*r**3/200+11*r*r/40+13*r/40-m.mpf(259)/400) if q==4 else 13*(m.sqrt(5)-5)/50
 result={'q':q,'method':'independent numerical implicit root solves and automatic multivariate differentiation, no manually supplied mark derivative arrays','precision_decimal_digits':m.mp.dps,'computed_c1':str(full),'symbolic_c1':str(target),'absolute_discrepancy':str(abs(full-target)),'H':[[str(H[i,j]) for j in range(h)] for i in range(h)],'D_sad':str(amp),'D_uni':str(univ)}
 reports.append(result);print(q,result['computed_c1'],result['absolute_discrepancy'],flush=True)
Path(__file__).with_suffix('.json').write_text(json.dumps(reports,indent=2)+'\n')
