import mpmath as mp,json
from pathlib import Path
mp.mp.dps=100
rows=[]
for t in map(mp.mpf,['.4','.7','1','1.5','2']):
 q=mp.exp(-t);delta=1-q;lam=-mp.log(delta);u=lam/t-mp.mpf('.5');Q=mp.exp(-4*mp.pi**2/t)
 kmax=int(mp.ceil((abs(lam)+270)/t))
 logF=mp.fsum(mp.log1p(mp.exp(-k*t)/delta) for k in range(1,kmax+1))
 logG=mp.fsum(mp.log1p(delta*mp.exp(-k*t)) for k in range(kmax+1))
 theta=mp.fsum(mp.exp(-2*mp.pi**2*m*m/t)*mp.cos(2*mp.pi*m*u)*(1 if m==0 else 2) for m in range(20))
 logEuler=mp.fsum(mp.log1p(-Q**k) for k in range(1,100))
 core=(lam*lam/2+mp.pi**2/6)/t-lam/2+t/12-logG
 error=logF-(core+mp.log(theta)-logEuler)
 if abs(error)>mp.mpf('1e-90'):raise RuntimeError('modular identity')
 rows.append({'t':str(t),'residual':str(error),'exact_log_correction':str(logF-core),'theta_leading':str(2*mp.exp(-2*mp.pi**2/t)*mp.cos(2*mp.pi*u))})
print(json.dumps(rows,indent=2));Path('modular_numeric_results.json').write_text(json.dumps(rows,indent=2))
