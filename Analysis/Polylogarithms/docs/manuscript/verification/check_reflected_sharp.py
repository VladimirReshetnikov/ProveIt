"""Independent moment-integral diagnostics for the cross-report sharp corollary."""
from pathlib import Path
import importlib.util,json,sys
import mpmath as mp
B=Path(__file__).resolve().parents[1]
source=B.parent/'reports/rigidity-and-reflected-moments/code/verify_reflected_moments.py'
spec=importlib.util.spec_from_file_location('incoming_reflected_numeric',source)
m=importlib.util.module_from_spec(spec);sys.modules[spec.name]=m;spec.loader.exec_module(m)
mp.mp.dps=180
tau,rho,alpha,v,C,b,beta=m.critical_constants()
rows=[]
for n in [20,40,60]:
 N=int(mp.nint((n+mp.mpf('1.5'))/alpha));eta=N*alpha-n
 for reflected in [1,2,3]:
  coefficients=[mp.mpf(0)]+[m.numeric_A(k,reflected) for k in range(1,N+1)]
  exact_integral=m.normalized_moment(n,reflected)
  first_omitted=coefficients[N]/mp.mpf(N)**n
  remainder=exact_integral-mp.fsum(coefficients[k]/mp.mpf(k)**n for k in range(1,N))
  ratio=remainder/first_omitted
  first=mp.mpf('.5')+(3-2*eta)/(8*N)
  second=first+(beta[reflected]/4+alpha*(6*eta-13)/96)/N**2
  passed=ratio>0 and abs(ratio-mp.mpf('.5'))<mp.mpf('.02') and abs(ratio-second)<abs(ratio-first)
  assert passed,(n,reflected,ratio,first,second)
  rows.append(dict(n=n,m=reflected,N=N,eta=mp.nstr(eta,30),ratio=mp.nstr(ratio,55),
   first_prediction=mp.nstr(first,45),second_prediction=mp.nstr(second,45),
   N_cubed_error_after_second=mp.nstr((ratio-second)*N**3,30),passed=bool(passed)))
  print(n,reflected,N,mp.nstr(ratio,18),flush=True)
result=dict(engine='mpmath '+mp.__version__,working_precision=mp.mp.dps,
 scope='Finite numerical diagnostics of the written asymptotic corollary, not interval bounds or a proof of universal constants.',
 checks=rows,all_pass=all(x['passed'] for x in rows))
(B/'verification/reflected-sharp-results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
