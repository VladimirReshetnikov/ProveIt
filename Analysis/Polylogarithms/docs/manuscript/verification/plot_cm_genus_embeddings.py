"""Illustrate the proved CM embedding behavior with finite lattice sums."""
from pathlib import Path
import json, sys
import mpmath as mp
B=Path(__file__).resolve().parents[1]
local=B/'verification/.scratch-plotdeps'
if local.is_dir():sys.path.insert(0,str(local))
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
mp.mp.dps=100
N=10;M=20
principal=(-1+1j*mp.sqrt(15))/2
other=(-1+1j*mp.sqrt(15))/4
def terms(tau):
    values=[mp.mpc(1)/k**12 for k in range(1,M+1)]
    values.extend((m+n*tau)**(-12) for n in range(1,N+1) for m in range(-M,M+1))
    return values
bases=[terms(principal),terms(other)];current=[row[:] for row in bases]
rows=[]
for m in range(1,81):
    vals=[2*mp.fsum(row) for row in current]
    r=abs(vals[0])/abs(vals[1]);log_conjugate=-12*m*mp.log10(2)-mp.log10(r)
    rows.append(dict(m=m,weight=12*m,ratio=mp.nstr(r,45),
        log10_conjugate=mp.nstr(log_conjugate,45),
        leading_denominator=mp.nstr(4*abs(mp.cos(6*m*mp.arg(other))),35)))
    current=[[value*base for value,base in zip(row,bb)] for row,bb in zip(current,bases)]
exact=(mp.mpf(34829)+15576*mp.sqrt(5))/1216
assert abs(mp.mpf(rows[0]['ratio'])-exact)<mp.mpf('1e-7')
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':9,'pdf.fonttype':42})
fig,axes=plt.subplots(1,2,figsize=(10.5,3.6),layout='constrained')
ms=[r['m'] for r in rows]
axes[0].semilogy(ms,[float(r['ratio']) for r in rows],'.-',lw=.7,color='#1d7874',ms=4)
axes[0].axhline(.5,color='#555',ls='--',lw=.8,label='Proved liminf = 1/2')
axes[0].set_title('Physical quadratic embedding');axes[0].set_ylabel('Absolute genus ratio')
axes[0].legend(frameon=False,fontsize=8)
axes[1].plot(ms,[float(r['log10_conjugate']) for r in rows],color='#bc6c25',lw=1)
axes[1].set_title('The conjugate from the exact norm law');axes[1].set_ylabel('log10 of the conjugate')
for ax in axes:ax.set_xlabel('m, with modular weight 12m');ax.grid(alpha=.2)
(B/'figures').mkdir(exist_ok=True)
fig.savefig(B/'figures/cm_genus_embeddings.pdf',bbox_inches='tight')
fig.savefig(B/'figures/cm_genus_embeddings.png',dpi=160,bbox_inches='tight')
out=dict(working_precision=100,lattice_rectangle=dict(n=N,m=M),
    first_ratio_exact_comparison_residual=mp.nstr(abs(mp.mpf(rows[0]['ratio'])-exact),30),
    rows=rows,scope='Finite lattice numerical illustrations; exact degree, norm and cluster-set results have separate analytic proofs. Arithmetic rounding is not enclosed.')
(B/'verification/CM-genus-plot.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('Rendered 80 genus ratios; first exact comparison residual',out['first_ratio_exact_comparison_residual'])
