import json,sys
from pathlib import Path
import mpmath as mp
sys.path.insert(0,str(Path(__file__).parent))
from checks import parameters,h_coefficients
mp.mp.dps=80
x=json.load(open(Path(__file__).with_name('checks.json')))
rows=[]
for row in x['rows']:
 if row['alpha'] not in ['1','2'] or row['n']<1000:continue
 n=row['n'];alpha=int(row['alpha']);exact=mp.mpf(row['log_exact'])
 u,A,N,t,s=parameters(n,alpha);ell=mp.log(u);h=h_coefficients(u,9)
 total=mp.mpc(0)
 errors=[]
 for K in range(9):
  Ak=A-2*mp.pi**2*K**2+2j*mp.pi*K*ell
  tk=mp.sqrt(Ak/N);sk=mp.sqrt(Ak*N)
  val=(-1)**K*sum(h[m]*tk**(m+1)*mp.besseli(m+1,2*sk) for m in range(10))
  total+=val if K==0 else 2*mp.re(val)
  approx=mp.re(total)/mp.sqrt(1+u)
  error=approx/mp.exp(exact)-1
  errors.append(mp.nstr(error,15))
 rows.append({'alpha':alpha,'n':n,'relative_errors_K0_through8':errors})
print(json.dumps(rows,indent=2))
with open(Path(__file__).with_name('resonance-checks.json'),'w') as f:json.dump(rows,f,indent=2)
