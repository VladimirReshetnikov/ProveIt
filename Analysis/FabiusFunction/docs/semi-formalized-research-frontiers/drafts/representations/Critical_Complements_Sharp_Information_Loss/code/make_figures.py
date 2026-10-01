#!/usr/bin/env python3
"""Create the article's figures and table fragments from saved diagnostics."""
from pathlib import Path
import argparse
import csv
import numpy as np
import matplotlib
matplotlib.use('Agg')
matplotlib.rcParams['pdf.fonttype']=42
import matplotlib.pyplot as plt
from scipy.special import lambertw

ROOT=Path(__file__).resolve().parents[1]
# ed. (2026-09-30): it read and wrote the recorded data/ and figures/; it now
# reads <output-dir>/data and writes <output-dir>/figures and <output-dir>/data
# (default <package>/rerun, where code/verify.py writes by default). Pass
# --output-dir . from the package directory to regenerate the recorded files.
_parser=argparse.ArgumentParser(description=__doc__)
_parser.add_argument('--output-dir',type=Path,default=ROOT/'rerun')
OUT=_parser.parse_args().output_dir
(OUT/'figures').mkdir(parents=True,exist_ok=True)

def read(name):
    with (OUT/'data'/name).open() as f:
        return [{k:float(v) for k,v in r.items()} for r in csv.DictReader(f)]

c=np.geomspace(.015,20,350)
z=1/(2*c)
arg=-np.exp(-1-z)
C=c*(-lambertw(arg,-1).real+lambertw(arg,0).real)
fig,ax=plt.subplots(figsize=(7.0,4.1))
ax.plot(c,C,label=r'$C(c)$: critical-complement profile',linewidth=1.8)
ax.plot(c,2*np.sqrt(c),'--',label=r'$2\sqrt{c}$: Gaussian approximation')
ax.axhline(.5,linestyle=':',label=r'$1/2$: thin-complement limit')
ax.set_xscale('log');ax.set_yscale('log')
ax.set_xlabel(r'$c=m/\log n$');ax.set_ylabel('Leading overlap coefficient')
ax.legend(loc='upper left',fontsize=9)
ax.grid(True,alpha=.25)
fig.tight_layout()
fig.savefig(OUT/'figures'/'crossover.pdf',bbox_inches='tight')
plt.close(fig)

rows=read('finite_geometric_metrics.csv')
n=np.array([r['n'] for r in rows])
fig,ax=plt.subplots(figsize=(7.0,4.1))
ax.plot(n,[-r['scaled_overlap_residual'] for r in rows],'o-',
        label='Measured scaled deficit')
ax.plot(n,[r['boundary_deficit'] for r in rows],'s--',
        label=r'Boundary correction $\Delta_0(\varepsilon_n)$')
ax.set_xscale('log',base=2)
ax.set_xlabel(r'Effective bulk size $n$')
ax.set_ylabel('Deficit from the two-term overlap formula')
ax.legend(fontsize=9);ax.grid(True,alpha=.25)
fig.tight_layout()
fig.savefig(OUT/'figures'/'boundary_deficit.pdf',bbox_inches='tight')
plt.close(fig)

br=read('boundary_constants.csv')
lines=[]
for r in br:
    if r['m']==0 or r['rho']==1:
        lines.append(f"{r['rho']:.2f} & {int(r['m'])} & {r['K']:.9f} & "
                     f"{r['entropy']:.9f} & {r['information_gap']:.9f} \\\\")
# ed. (2026-09-30): newline='\n' here and below, so the fragments are LF on every platform.
(OUT/'data'/'boundary_table.tex').write_text('\n'.join(lines)+'\n',newline='\n')
lines=[]
for r in rows:
    lines.append(f"{int(r['n'])} & {r['overlap']:.9f} & "
                 f"{r['scaled_overlap_residual']:.6f} & "
                 f"{r['kl']:.9f} & {r['n']*r['kl_residual']:.6f} \\\\")
(OUT/'data'/'finite_table.tex').write_text('\n'.join(lines)+'\n',newline='\n')
print('Wrote two PDF figures and two LaTeX table fragments.')
