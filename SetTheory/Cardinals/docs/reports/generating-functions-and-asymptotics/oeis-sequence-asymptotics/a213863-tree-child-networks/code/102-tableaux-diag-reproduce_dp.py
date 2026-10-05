"""Exact integer DP with explicitly non-certified high-precision numerical evaluation."""
import json,sys,time
from pathlib import Path
import sympy as S, mpmath as mp
BASE=Path(__file__).resolve().parent
N=int(sys.argv[1]) if len(sys.argv)>1 else 3000
if N < 2: raise ValueError('N must be at least 2')
mp.mp.dps=75
aa=mp.airyaizero(1);a=S.symbols('a')
data=json.load(open(BASE/'endpoint_9.json'))
co=[mp.mpf(str(S.N(S.sympify(z).subs(a,str(aa)),80))) for z in data['log_correction']]
rc=[mp.mpf(str(S.N(S.sympify(z).subs(a,str(aa)),80))) for z in data['ratio']]
old=[1];prev=1;rows=[];start=time.time()
samples={100,500,1000,1500,2000,2500,3000}|set(range(max(10,N-900),N+1,100))
for n in range(2,N+1):
 ss=0;new=[]
 for m in range(1,n+1):
  if m<=n-1:ss+=old[m-1]
  new.append((2*n+m-2)*ss)
 val=sum(new)
 if n in samples:
  z=mp.mpf(n)**(-mp.mpf(1)/3)
  logu=mp.log(val)-mp.loggamma(n+1)-n*mp.log(12)-aa*(3*mp.mpf(n))**(mp.mpf(1)/3)+mp.mpf(2)/3*mp.log(n)
  gs=[mp.exp(logu-sum(co[j-1]*z**j for j in range(1,d+1))) for d in range(7)]
  q=mp.mpf(val)/prev/(12*n)
  errors=[q-sum(rc[j]*z**j for j in range(d+1)) for d in [3,4,5,6,7,8,9]]
  row={'n':n,'log_normalized':mp.nstr(logu,70),'gamma_corrections_0_through_6':[mp.nstr(g,55) for g in gs],'ratio_error_orders_3_through_9':[mp.nstr(e,55) for e in errors]}
  rows.append(row)
  print(n, 'gamma corrected six=',row['gamma_corrections_0_through_6'][-1],flush=True)
 old=new;prev=val
out={'disclaimer':'Integer recurrence exact. mpmath evaluation and extrapolation are consistency diagnostics, not certified amplitude bounds.','N':N,'mp_precision':mp.mp.dps,'seconds':time.time()-start,'samples':rows}
destination=BASE/(sys.argv[2] if len(sys.argv)>2 else f'replayed_dp_{N}.json')
if destination.exists(): raise FileExistsError('Refusing to overwrite '+str(destination))
json.dump(out,open(destination,'w'),indent=2)
print('done',time.time()-start)
