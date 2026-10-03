"""P1-only diagnostics against exact truncated integer rows.
Numerical ratios and constants are not certified enclosures.
"""
from pathlib import Path
import json
import mpmath as mp
ROOT=Path(__file__).resolve().parents[1]
mp.mp.dps=65
rows=json.loads((ROOT/'results/exact-truncated-rows.json').read_text())['rows']
constants=json.loads((ROOT/'results/independent-constants.json').read_text())['constants']
R,A,K,gamma,c,B=[mp.mpf(constants[key]) for key in ('R','A','K','gamma0','c','B')]
checks=[]
for n,k in [(125,5),(160,5),(216,6),(320,7),(343,7),(512,8),(640,9)]:
    eps=mp.mpf(n)**(-mp.mpf(1)/3);lam=k*eps
    exact=mp.mpf(rows[n][k])
    carrier=gamma/(2*mp.sqrt(mp.pi))*R**(-n)*mp.mpf(n)**(-mp.mpf('1.5'))*(c*n)**(2*k)/mp.factorial(2*k)*mp.exp(-2*gamma*lam**mp.mpf('1.5'))
    ratio=exact/carrier;p1=gamma*mp.sqrt(lam)/4+B*lam*lam
    checks.append({'n':n,'k':k,'lambda':mp.nstr(lam,25),'exact_integer':str(rows[n][k]),
        'exact_div_carrier':mp.nstr(ratio,30),'scaled_first_residual':mp.nstr((ratio-1)/eps,25),
        'P1':mp.nstr(p1,25),'leading_relative_error':mp.nstr(1/ratio-1,25),
        'first_corrected_relative_error':mp.nstr((1+eps*p1)/ratio-1,25)})
output={'counts':'exact integers modulo u^13, n<=640','numerical_evaluation':'non-certified 65-digit arithmetic','checks':checks}
(ROOT/'results/p1-diagnostics.json').write_text(json.dumps(output,indent=2)+'\n')
selected=[item for item in checks if item['n'] in (125,216,343,512)]
header=r'\begin{tabular}{rrrrr}'+'\n'+r'\toprule'+'\n'+r'$n$&$k$&$\lambda$&$(E/\mathcal L-1)/\eps$&$P_1(\lambda)$\\'+'\n'+r'\midrule'+'\n'
lines=[]
for row in selected:
    lines.append(f"{row['n']} & {row['k']} & 1 & {float(row['scaled_first_residual']):+.8f} & {float(row['P1']):+.8f} "+r'\\')
footer=r'\bottomrule'+'\n'+r'\end{tabular}'+'\n'
(ROOT/'results/p1-table.tex').write_text(header+'\n'.join(lines)+'\n'+footer)
print(json.dumps(output,indent=2))
