from pathlib import Path
SCRIPT_DIR = Path(__file__).resolve().parent
RESULT_DIR = SCRIPT_DIR.parent / "results"
RESULT_DIR.mkdir(exist_ok=True)
import contextlib,io,runpy,math,json
import mpmath as mp
with contextlib.redirect_stdout(io.StringIO()): d=runpy.run_path(str(SCRIPT_DIR / 'check_scores.py'))
mp.mp.dps=60
lam=d['lam'];mu=d['mu'];N=d['N'];p=1-mp.exp(-lam);c=mp.exp(-lam)*mu
# Avoid rounding cancellation in R by exact integer numerator first.
def rn(j): return mp.mpf(2*j*N[j]-math.comb(2*j,j))/(2*j*j)
e2=-mp.log(2)/2-mp.mpf(1)/4+sum(rn(j)*j*(j-1)/mp.mpf(4)**j for j in range(1,250))/2
ell=(mu**2/2-e2)/mu;k=2/(3*mu)
c2plus=mp.mpf(1)/128+mp.mpf(35)/8*mu**2+mp.mpf(63)/16*mu+mp.mpf(35)/4*e2
c2minus=mp.mpf(1)/128+mp.mpf(35)/8*mu**2-mp.mpf(63)/16*mu-mp.mpf(35)/4*e2
rows=json.load(open(str(RESULT_DIR / 'crossover-checks.json')))['checks']
for row in rows:
 n=row['n'];tau=mp.mpf(row['tau']);a=mp.mpf(n)*c/(n*p+tau*c)
 C2=mp.exp(-tau)*(tau**2/2-tau-ell*(tau**2-2*tau)+k*k*(-3*tau+3*tau**2-tau**3/2))
 model2=mp.mpf(row['two_term_model'])+C2/(n*a)
 row['three_term_model']=float(model2);row['higher_scaled_residual']=float(mp.mpf(n)**mp.mpf('1.5')*(mp.mpf(row['actual'])-model2))
 row['higher_relative_error']=float(mp.mpf(row['actual'])/model2-1)
out={'e2':str(e2),'ell':str(ell),'fixed_score_c2':str(c2plus),'fixed_strong_c2':str(c2minus),'checks':rows}
open(str(RESULT_DIR / 'higher-crossover-checks.json'),'w').write(json.dumps(out,indent=2))
print('e2',e2,'ell',ell,'fixed c2',c2plus,c2minus)
for row in rows: print(row['n'],round(row['tau'],3),row['higher_scaled_residual'],row['higher_relative_error'])
