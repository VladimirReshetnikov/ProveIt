from pathlib import Path
SCRIPT_DIR = Path(__file__).resolve().parent
RESULT_DIR = SCRIPT_DIR.parent / "results"
RESULT_DIR.mkdir(exist_ok=True)
import contextlib,io,runpy,math,json
import mpmath as mp
with contextlib.redirect_stdout(io.StringIO()): d=runpy.run_path(str(SCRIPT_DIR / 'check_scores.py'))
mp.mp.dps=50
I=d['I'];lam=d['lam'];mu=d['mu'];p=1-mp.exp(-lam);c=mp.exp(-lam)*mu
inc=[float(mp.mpf(v)/mp.mpf(4)**k) for k,v in enumerate(I)]
rows=[]
for n in [100,300,1000]:
 center=mp.log(n)/2+2*mp.log(mp.log(n))+mp.log(mu*mp.sqrt(mp.pi)/2)
 for tau in [mp.mpf(0),mp.mpf(1),mp.mpf(3),center-2,center,center+2,2*mp.log(n)]:
  u=mp.mpf(n)/(n*p+tau*c);a=u*c;k=2/(3*mu)
  W=[1.0]+[0.0]*n
  for j in range(1,n+1):W[j]=float(u)*sum(inc[i]*W[j-i] for i in range(1,j+1))
  H=mp.hyp1f1(2,mp.mpf('.5'),-tau)/mp.sqrt(mp.pi)
  model=(mp.exp(-tau)+k*H/mp.sqrt(n))/a
  ratmodel=((1+tau/n)**(-n-1)+k*H/mp.sqrt(n))/a
  rows.append({'n':n,'tau':float(tau),'u':float(u),'actual':W[n],'two_term_model':float(model),'relative_error':float(mp.mpf(W[n])/model-1),'n_times_absolute_residual':float(n*(mp.mpf(W[n])-model)),'exact_carrier_residual':float(n*(mp.mpf(W[n])-ratmodel))})
out={'checks':rows,'notes':'Actual normalized coefficients from the exact irreducible renewal recurrence, double-precision numerical check only; model constants and H evaluated at50decimal precision.'}
open(str(RESULT_DIR / 'crossover-checks.json'),'w').write(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
