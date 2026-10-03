#!/usr/bin/env python3
"""Render actual finite visited sets; simulator is the authored local CA rule."""
from pathlib import Path
import argparse, importlib.util, os, tempfile
_cache = tempfile.TemporaryDirectory(prefix='report30-figure-cache-')
os.environ['MPLCONFIGDIR'] = _cache.name
os.environ['XDG_CACHE_HOME'] = _cache.name
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]
p = argparse.ArgumentParser()
p.add_argument('--output-dir', type=Path, required=True)
a = p.parse_args()
out = a.output_dir.resolve()
if out == ROOT or ROOT in out.parents:
    raise RuntimeError('Figure output must be external to the release')
out.mkdir(parents=True, exist_ok=True)
spec = importlib.util.spec_from_file_location('geometry_audit', ROOT/'scientific/geometry/audit.py')
rule = importlib.util.module_from_spec(spec)
spec.loader.exec_module(rule)

def collect(tmax, drift):
    state=rule.initial(3)
    sites={key:set() for key in ('Left marker','Head','Right marker')}
    for t in range(tmax+1):
        for (x,y),symbol in state.items():
            key='Head' if symbol in ('E','W') else ('Left marker' if x==0 else 'Right marker')
            sites[key].add((x,y+t*drift))
        state=rule.step(state,True)
    return sites

plt.rcParams.update({'font.family':'DejaVu Sans','font.size':9,'axes.spines.top':False,'axes.spines.right':False,'pdf.fonttype':42})
fig,axes=plt.subplots(1,2,figsize=(7.4,3.8),gridspec_kw={'width_ratios':[1.05,1]})
colors={'Left marker':'#4B6C8B','Head':'#262626','Right marker':'#B65C2B'}
for ax,data,title in zip(axes,[collect(rule.T(15,3),0),collect(180,1)],['Stationary frame','Restored vertical drift']):
    for key in ('Head','Left marker','Right marker'):
        coords=sorted(data[key]); xs,ys=zip(*coords)
        ax.scatter(xs,ys,s=8 if key=='Head' else 13,c=colors[key],label=key,linewidths=0,zorder=3 if key!='Head' else 2)
    ax.set_title(title,pad=10,fontsize=10,weight='bold')
    ax.set_xlabel('Horizontal coordinate x'); ax.set_ylabel('Vertical coordinate y')
    ax.grid(color='#E1E1E1',linewidth=.45,zorder=0)
    ax.set_xlim(-.6,19 if ax is axes[0] else 16)
axes[0].set_ylim(-.6,16); axes[0].set_aspect('equal',adjustable='box')
axes[1].set_ylim(-3,200)
handles,labels=axes[1].get_legend_handles_labels()
fig.legend(handles,labels,loc='lower center',ncol=3,frameon=False,bbox_to_anchor=(.5,-.015),fontsize=8)
fig.subplots_adjust(left=.08,right=.985,top=.9,bottom=.18,wspace=.32)
fig.savefig(out/'visited-geometry.pdf',metadata={'CreationDate':None,'ModDate':None})
fig.savefig(out/'visited-geometry.png',dpi=180)
print('Rendered actual simulator point sets')
