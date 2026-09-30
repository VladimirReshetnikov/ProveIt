#!/usr/bin/env python3
"""Generate article figures from recorded diagnostics and profile quadrature.

Editorial amendment (ProveIt, 2026-09-29): outputs go to --output-dir
(default build/, relative to the package root), as figures/*.png, figures/*.pdf
and data/figure_curve.json below it. Pass --output-dir . to overwrite the
shipped figures and data/figure_curve.json, as the delivered script always did.
"""
import argparse
import json
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from verify import profile_ratio
ROOT=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output-dir',type=Path,default=Path('build'),help='output root; relative paths are resolved against the package root (default: build)')
args=parser.parse_args()
OUT=args.output_dir if args.output_dir.is_absolute() else ROOT/args.output_dir
(OUT/'figures').mkdir(parents=True,exist_ok=True);(OUT/'data').mkdir(parents=True,exist_ok=True)
plt.rcParams['pdf.fonttype']=42
plt.rcParams['ps.fonttype']=42
report=json.loads((ROOT/'data/verification_results.json').read_text())
fig,ax=plt.subplots(figsize=(6.4,3.8))
rows=[r for r in report['coefficient_diagnostics'] if r['lambda']==1.]
for k,label in [(0,'Leading Landau profile'),(1,'Through first correction'),(2,'Through second correction')]:
    ax.loglog([r['n'] for r in rows],[abs(r[f'relative_error_{k}']) for r in rows],marker='o',label=label)
ax.set_xlabel('Coefficient index n');ax.set_ylabel('Absolute relative error')
ax.legend(fontsize=8);ax.grid(True,which='both',alpha=.25);fig.tight_layout()
fig.savefig(OUT/'figures/correction_errors.png',dpi=220)
fig.savefig(OUT/'figures/correction_errors.pdf');plt.close(fig)
fig,ax=plt.subplots(figsize=(6.4,3.8))
curve=[]
for lam in [1.,4.]:
    ms=np.linspace(.25,2.5,40)
    rs=[profile_ratio(lam,float(m))[0] for m in ms]
    ax.plot(ms,rs,label=fr'Limiting profile, $\lambda={lam:g}$')
    rows=[r for r in report['cutoff_diagnostics'] if r['lambda']==lam]
    ax.scatter([r['M_delta'] for r in rows],[r['ratio'] for r in rows],marker='x',s=35,label=fr'$n=2048$, $\lambda={lam:g}$')
    curve.extend({'lambda':lam,'m':float(m),'R':float(r)} for m,r in zip(ms,rs))
ax.set_xlabel(r'Scaled action cutoff $m=M\delta$');ax.set_ylabel('Retained coefficient fraction')
ax.set_ylim(-.03,1.03);ax.legend(fontsize=8);ax.grid(True,alpha=.25);fig.tight_layout()
fig.savefig(OUT/'figures/cutoff_profile.png',dpi=220)
fig.savefig(OUT/'figures/cutoff_profile.pdf');plt.close(fig)
(OUT/'data/figure_curve.json').write_text(json.dumps(curve,indent=2)+'\n',newline='\n')
print(f'Wrote figures and figure_curve.json under {OUT}')
