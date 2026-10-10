"""Independent Mellin quadrature diagnostics for the frozen S10 vector."""
from pathlib import Path
import json,time,sys
import mpmath as m
BASE=Path(__file__).resolve().parent
r=next(v for v in json.loads((BASE/'gaussian_candidates.json').read_text())['candidates'] if v['p']==10)
r['frozen_vector']=r['vector']
dps=int(sys.argv[1]) if len(sys.argv)>1 else 120
m.mp.dps=dps;t=time.time();cuts=[m.mpf(0),m.mpf(1)/8,m.mpf(1)/2,m.mpf(1)]
# Change x=e^{-t}: explicitly integrate t on [0,1,4,16,infinity].
cuts_t=[m.mpf(0),m.mpf(1),m.mpf(4),m.mpf(16),m.inf]
S=-m.quad(lambda t:t**9*m.exp(-t)*m.log1p(m.exp(-2*t))/(1+m.exp(-2*t)),cuts_t)/m.factorial(9)
print('S10 Mellin done',time.time()-t,flush=True)
vals=[S]
for a in [10,8,6,4,2]:
 b=11-a
 if b==1:
  g=-m.quad(lambda x:(-m.log(x))**(a-2)*m.log1p(x*x)*m.atan(x)/x,cuts)/(2*m.factorial(a-2))
 else:
  g=m.im(m.quad(lambda x:(-m.log(x))**(a-1)*m.j*m.polylog(b,m.j*x)/(1-m.j*x),cuts))/m.factorial(a-1)
 vals.append(g);print('g',a,b,'done',time.time()-t,flush=True)
beta=lambda s:(m.zeta(s,m.mpf(1)/4)-m.zeta(s,m.mpf(3)/4))/m.mpf(4)**s
vals +=[m.pi**11]+[beta(2*j)*m.zeta(11-2*j) for j in range(1,5)]+[beta(10)*m.log(2)]
out={'status':'independent Mellin diagnostics; no rigorous quadrature-error claim','digits':dps,'basket':r['basket'],'vector':r['frozen_vector'],'values':[m.nstr(v,dps-10) for v in vals],'integer_residual':m.nstr(m.fdot(vals,r['frozen_vector']),80),'normalized_residual':m.nstr(m.fdot(vals,r['frozen_vector'])/r['frozen_vector'][0],80),'seconds':time.time()-t}
(BASE/'s10_mellin_audit.json').write_text(json.dumps(out,indent=2)+'\n')
print('done',out['seconds'],'residual',out['normalized_residual'],flush=True)
