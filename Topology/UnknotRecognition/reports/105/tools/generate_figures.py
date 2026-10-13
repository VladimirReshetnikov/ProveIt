"""Generate the article's exact-count figure from archived results."""
import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
report = json.loads((ROOT/'results/whole_audit.json').read_text())
counts = report['counts']
canonical = [100, counts['historical/canonical/COMPLETE']]
deferred = [106, counts['historical/deferred/COMPLETE']]
plt.rcParams.update({'font.family':'DejaVu Serif', 'font.size':9,
                     'axes.titlesize':10, 'axes.labelsize':9,
                     'legend.fontsize':8, 'pdf.fonttype':42,
                     'axes.spines.top':False, 'axes.spines.right':False})
fig, axs = plt.subplots(1,2,figsize=(7.05,3.15),layout='constrained')
blue, orange = '#173d59', '#c16d33'
x = np.arange(2)
for vals, offset, color, label in [(canonical,-.18,blue,'Canonical'),
                                    (deferred,.18,orange,'Deferred')]:
    bars = axs[0].bar(x+offset,vals,.34,color=color,label=label)
    axs[0].bar_label(bars,padding=3,fontsize=9)
axs[0].set_xticks(x,['Core','Whole cut'])
axs[0].set_ylim(0,120)
axs[0].set_ylabel('Complete certificates (106 cases)')
axs[0].set_title('Historical native coverage',loc='left',fontweight='bold')
axs[0].legend(loc='upper center',bbox_to_anchor=(.5,-.13),ncol=2,frameon=False)
axs[0].set_axisbelow(True)
axs[0].grid(axis='y',alpha=.15)
h = np.arange(1,17)
axs[1].semilogy(h,[(3**int(k)+1)//2 for k in h],color=blue,lw=1.8,
                label='Unpruned forest trials')
axs[1].semilogy(h,5*h,color=orange,lw=1.8,label='Deferred incidence visits')
axs[1].set_xlabel('Theta blocks h')
axs[1].set_ylabel('Exact count (log scale)')
axs[1].set_xticks([1,4,8,12,16])
axs[1].set_title('Specified family work counts',loc='left',fontweight='bold')
axs[1].legend(loc='upper left',frameon=False)
axs[1].grid(axis='y',alpha=.15)
out = ROOT/'article/figures/research_results.pdf'
fig.savefig(out,metadata={'Title':'Native coverage and exact theta-family work counts',
                         'Author':'ProveIt research continuation','CreationDate':None})
fig.savefig(out.with_suffix('.png'),dpi=180)
print(out)
