#!/usr/bin/env python3
"""Regenerate the plot and numerical tables (not proof certificates)."""
from pathlib import Path
import json
import math
import mpmath as mp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from verify import orders, spectral_parameters, omega_table, z_value

base=Path(__file__).parent
out=base/'data'; out.mkdir(exist_ok=True)
rs=orders(1000)
k=list(range(1,1001))
fig,ax=plt.subplots(figsize=(6.8,3.3))
ax.plot(k,[rs[j]/math.comb(j+3,3) for j in k],label='Exact minimal / unreduced order')
ax.axhline(80/(9*math.pi**2),linestyle='--',label=r'$80/(9\pi^2)$')
ax.set_xscale('log');ax.set_xlabel('Column index k (logarithmic scale)')
ax.set_ylabel('Recurrence-order ratio');ax.legend(frameon=False,fontsize=9)
fig.tight_layout();fig.savefig(out/'order_ratio.pdf');fig.savefig(out/'order_ratio.png',dpi=160)
plt.close(fig)
report=json.loads((out/'verification_report.json').read_text())
rows=[]
for a in report['numerical_diagnostics']['samples']:
 rows.append(f"{a['n']} & {a['k']} & {float(a['relative_error']):.3e} & "+
             f"{float(a['rigorous_formula_bound_evaluated_numerically']):.3e} & "+
             f"{float(a['log_concavity_log_ratio']):.6f} \\\\")
(out/'asymptotic_table.tex').write_text('\n'.join(rows)+'\n')
mp.mp.dps=80
cross=[]
for n in [1000,10000,100000]:
 for target in [-1,0,1]:
  M=int(mp.nint(n/(mp.log(n)+target)-mp.mpf('0.5')))
  rho,alpha,delta=spectral_parameters(M)
  s=n/(mp.mpf(M)+mp.mpf('0.5'))-mp.log(n)
  q=mp.exp(-n*delta)
  val=mp.mpf(0)
  # The omitted j>=100 tail is bounded by C sum_{j>=100} ((n+1)q)^j/j!.
  for j in range(min(M,100)):
   rr,aa,_=spectral_parameters(M-j)
   val+=(-1)**j*mp.binomial(n+1,j)*(aa/alpha)*mp.exp(n*mp.log(rr/rho))
  K=(n+1)*q
  tail=2*mp.e**K*K**100/mp.factorial(100)
  spectral=8*mp.power(2,-n)*mp.e**K
  limit=mp.exp(-mp.exp(-s))
  cross.append({'n':n,'k':M-1,'s_n':mp.nstr(s,16),
                'ratio_from_perron_sum':mp.nstr(val,16),
                'crossover_prediction':mp.nstr(limit,16),
                'analytic_remainder_excluding_roundoff_numerically_evaluated':mp.nstr(tail+spectral,8)})
(out/'crossover_diagnostics.json').write_text(json.dumps(cross,indent=2)+'\n')
(out/'crossover_table.tex').write_text('\n'.join(
 f"{r['n']} & {r['k']} & {float(r['s_n']):.5f} & "+
 f"{float(r['ratio_from_perron_sum']):.8f} & {float(r['crossover_prediction']):.8f} \\\\\n"
 for r in cross))
om=omega_table(19,4)
print('Column 3 at index14:',z_value(om,19,3))
print(json.dumps(cross,indent=2))
