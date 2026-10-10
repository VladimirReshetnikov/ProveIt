"""Plot the proved axis geometry using labeled numerical special-function values."""
from pathlib import Path
import json, sys
import mpmath as mp
B=Path(__file__).resolve().parents[1]
local=B/'verification/.scratch-plotdeps'
if local.is_dir():sys.path.insert(0,str(local))
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
mp.mp.dps=40
C=lambda b:-2*mp.im(mp.j*mp.polylog(b,mp.j)/(1-mp.j))
points=[mp.mpf('0.02')+mp.mpf('4.98')*j/179 for j in range(180)]
rows=[dict(b=mp.nstr(b,25),value=mp.nstr(C(b),35)) for b in points]
explore=json.loads((B/'verification/Gaussian-axis-exploration.json').read_text())
peak=mp.mpf(explore['axis_stationary_inner_order'])
critical=mp.pi/4+mp.log(2)/2
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'pdf.fonttype':42})
fig,ax=plt.subplots(figsize=(8.2,3.8),layout='constrained')
ax.axvspan(1,2,color='#258f8b',alpha=.10,label='Proved stationary-point bracket: 1 < b* < 2')
ax.plot([float(r['b']) for r in rows],[float(r['value']) for r in rows],color='#183b50',lw=1.8,label='C(b) = beta(b) + 2^(-b) eta(b)')
ax.axhline(float(critical),color='#c87528',ls='--',lw=1.2,label='Sharp critical Euler constant')
ax.scatter([float(peak)],[float(C(peak))],color='#258f8b',s=28,zorder=4)
ax.annotate('Numerical maximum: b* ≈ 1.302217',xy=(float(peak),float(C(peak))),
            xytext=(2.1,1.143),arrowprops={'arrowstyle':'->','color':'#555'},fontsize=9)
ax.set(xlabel='Inner order b',ylabel='Gaussian axis magnitude -2 g(0,b)',
       title='A unique nondegenerate maximum, proved by a three-power sign argument',
       xlim=(0,5),ylim=(1,1.151))
ax.grid(alpha=.18);ax.legend(loc='lower right',frameon=False,fontsize=8)
fig.savefig(B/'figures/Gaussian_axis_maximum.pdf',bbox_inches='tight')
fig.savefig(B/'figures/Gaussian_axis_maximum.png',dpi=170,bbox_inches='tight')
record=dict(working_precision=40,points=rows,numerical_peak=explore['axis_stationary_inner_order'],
 critical_constant=mp.nstr(critical,35),
 scope='Numerical curve and stationary-point marker; uniqueness, nondegeneracy, the (1,2) bracket and the critical constant have separate written proofs. No plotted decimals are certified.')
(B/'verification/Gaussian-axis-plot.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print('Rendered 180 Gaussian axis values with the proved bracket and critical constant.')
