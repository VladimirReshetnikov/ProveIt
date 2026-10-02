from pathlib import Path
SCRIPT_DIR = Path(__file__).resolve().parent
RESULT_DIR = SCRIPT_DIR.parent / "results"
RESULT_DIR.mkdir(exist_ok=True)
import json,mpmath as mp
from uniform_generator import coefficients,p,c
mp.mp.dps=50
rows=json.load(open(str(RESULT_DIR / 'crossover-checks.json')))['checks']
out=[]
for row in rows:
 n=row['n'];tau=mp.mpf(row['tau'])
 if not (tau>3 and tau<2*mp.log(n)-mp.mpf('.1')):continue
 target=mp.mpf(row['actual'])
 for M in [1,2,4]:
  def model(t):return (p/c+t/n)*sum(v/mp.mpf(n)**(mp.mpf(j)/2) for j,v in enumerate(coefficients(t)[:M+1]))
  root=mp.findroot(lambda t:model(t)-target,(tau-mp.mpf('.1'),tau+mp.mpf('.1')))
  u0=mp.mpf(n)/(n*p+tau*c);uhat=mp.mpf(n)/(n*p+root*c)
  out.append({'n':n,'tau':float(tau),'M':M,'tau_error':float(root-tau),'scaled_tau_error':float((root-tau)*mp.mpf(n)**(mp.mpf(M)/2)/mp.log(n)**2),'u_error':float(uhat-u0),'model_derivative':float(mp.diff(model,root))})
print(json.dumps(out,indent=2));open(str(RESULT_DIR / 'weight-inverse-checks.json'),'w').write(json.dumps(out,indent=2))
