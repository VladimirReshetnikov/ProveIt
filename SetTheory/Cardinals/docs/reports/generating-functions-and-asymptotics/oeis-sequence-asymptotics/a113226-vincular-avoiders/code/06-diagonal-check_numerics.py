#!/usr/bin/env python3
"""Numerical illustrations from exactly computed coefficients; not a proof."""
import json,pathlib
import mpmath as mp
ROOT=pathlib.Path(__file__).resolve().parent
mp.mp.dps=60
aa=json.loads((ROOT/'counts_600.json').read_text())
rho=mp.log(4); kappa=(mp.pi**2/(4*rho))**(mp.mpf(1)/3)
C=mp.exp(rho/2-3)*mp.sqrt(kappa/(3*mp.pi))
cs=[mp.mpf(v) for v in json.loads((ROOT/'saddle_checks.json').read_text())['numeric']]
rows=[]
for n in [50,100,200,400,600]:
    R=mp.exp(mp.log(aa[n])-mp.loggamma(n+1)+n*mp.log(rho)
             -3*kappa*n**(mp.mpf(1)/3)+mp.mpf(5)/6*mp.log(n))/C
    approximations=[sum(cs[j]*mp.mpf(n)**(-mp.mpf(j)/3) for j in range(K+1)) for K in range(4)]
    rows.append({'n':n,'normalized_exact':mp.nstr(R,22),
                 'approximations':[mp.nstr(v,22) for v in approximations],
                 'scaled_c1':mp.nstr((R-1)*mp.mpf(n)**(mp.mpf(1)/3),15)})
(ROOT/'numeric_regression.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows,indent=2))
