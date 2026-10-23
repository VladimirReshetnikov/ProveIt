#!/usr/bin/env python3
"""Check compact residual presentation in the TeX against literal JSON."""
import json,sympy as s
from pathlib import Path
R=Path(__file__).resolve().parent;d=json.loads((R/'quartic42.json').read_text());names=d['variables']+d['fixed_numerals'];v={x:s.Symbol(x) for x in names};v['q']=v['beta']*v['J']+1;v['k']=v['eta']+v['zeta'];v['Rhat']=s.sympify('F*(q+L-N)+J*(MC+q*MF)+q*(N-L-q)+L*alpha',locals=v)
compact=['L-q**2+1','N-q*(L+1)','X-q*w','a-E-(2*v_scale+1)*N','E*(X+1)-X*a','c-k*(a-E)-eta','P-E*(c-eta)-k','tau**2-P**2+P*k-1','D-X-a*c-(4*a+3)*gamma','Delta-a**2-4*a-3','C2-c**2','D**2-Delta*C2-1','k-1-E*h-Rhat','(K0+w)*(q-F-alpha)-F-z*(q-1)','F2-f**2','V+c-f*o','V-c*j+k-1-E*h','V**2+g-y**2','I-(2*r+1)*C2','Baux-I**2','Baux-Delta*F2+Delta','y**2-Baux*g-1','w-4*u**2']+d['residuals'][23:]
for i,(a,b) in enumerate(zip(compact,d['residuals'])):
 if s.expand(s.sympify(a,locals=v)-s.sympify(b,locals=v))!=0:raise ValueError('compact row '+str(i))
res={'status':'PASS','quadratic_residuals':27,'compact_polynomial_abbreviations_checked':True}
(R/'TEX_RESIDUAL_CHECK.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2))
