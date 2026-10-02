#!/usr/bin/env python3
import json,math
from pathlib import Path
import mpmath as mp
mp.mp.dps=70
root=Path(__file__).parent
exact=json.loads((root/'exact_values.json').read_text());data=json.loads((root/'asymptotic_coefficients.json').read_text())
rho=mp.mpf(data['rho']);c=mp.mpf(data['c']);C=3*c;D=mp.mpf(data['amplitude'])
a=[mp.mpf(x['decimal']) for x in data['coefficients']]
out=[]
for n in [20,50,100,200,400,557,700,1000]:
    if n>exact['max_n']:continue
    nf=mp.mpf(n);logexact=mp.log(mp.mpf(exact['a'][n]));base=mp.log(D)+mp.loggamma(n+1)-n*mp.log(rho)+C*mp.root(nf,3)-mp.mpf(5)/6*mp.log(nf)
    ratio=mp.exp(logexact-base);t=nf**(-mp.mpf(1)/3)
    scaled=[(ratio-sum(a[j]*t**j for j in range(k+1)))/t**(k+1) for k in range(len(a))]
    L=logexact;N=L/mp.lambertw(L/(mp.e*rho));ell=mp.log(N/rho);d=mp.log(D*mp.sqrt(2*mp.pi));alpha=-mp.mpf(1)/3
    aa=-C/ell;bb=mp.mpf(1)/3+(mp.log(rho)/3-d)/ell
    dd=-(aa*aa/2+C*aa/3+a[1])/ell
    ee=-((aa+C/3)*bb+alpha*aa+a[2]-a[1]**2/2)/ell
    x0=N+N**(mp.mpf(1)/3)*aa+bb
    x1=x0+N**(-mp.mpf(1)/3)*dd
    x2=x1+N**(-mp.mpf(2)/3)*ee
    out.append({'n':n,'ratio':str(ratio),'scaled_residuals':[str(x) for x in scaled],'inverse_error':[str(x0-n),str(x1-n),str(x2-n)]})
res={'constants':data,'checks':exact['checks'],'samples':out}
(root/'validation.json').write_text(json.dumps(res,indent=2)+'\n')
for row in out:print(row['n'],mp.nstr(mp.mpf(row['ratio']),12),[mp.nstr(mp.mpf(x),10) for x in row['scaled_residuals']], [mp.nstr(mp.mpf(x),9) for x in row['inverse_error']])
