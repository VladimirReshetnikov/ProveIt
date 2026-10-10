#!/usr/bin/env python3
"""Render the article's scientific diagnostic figure from stored JSON.

Requires matplotlib only. This script performs no new quadrature and makes
no certified error assertion. The plotted evidence is explicitly diagnostic.
"""
import json
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent.parent
harmonic = json.loads((ROOT/'code/harmonic/harmonic_diagnostics.json').read_text())
moments = json.loads((ROOT/'code/moments/joint_moment_diagnostics.json').read_text())
plt.rcParams.update({'font.family':'DejaVu Sans', 'font.size':9,
                     'axes.titlesize':10, 'axes.labelsize':9,
                     'legend.fontsize':8, 'pdf.fonttype':42,
                     'axes.spines.top':False, 'axes.spines.right':False})
colors = ['#243b62','#087f8c','#c46528']
styles = [('o','-'),('s','--'),('^','-.')]
fig, axes = plt.subplots(1,2,figsize=(7.1,3.15),layout='constrained')
rows=harmonic['inverse']
xx=[float(r['h']) for r in rows]
for key,label,color,(marker,style) in zip(
        ['leading_error','Q0_error','Q1_error'],
        ['Leading','With $Q_0$','With $Q_0+Q_1/h$'], colors, styles):
    axes[0].loglog(xx,[abs(float(r[key])) for r in rows],style,
                   marker=marker,color=color,markersize=4,label=label)
axes[0].set(title='Inverse harmonic threshold',xlabel='Harmonic depth $h$',
            ylabel='Absolute error in the exponent')
axes[0].legend(frameon=False,loc='lower left')
rows=sorted((r for r in moments['rows'] if r['s']==0),key=lambda r:r['m'])
xx=[r['m'] for r in rows]
errors=[[abs(float(r['leading'])/float(r['actual'])-1) for r in rows],
        [float(r['relative_first_error']) for r in rows],
        [float(r['relative_second_error']) for r in rows]]
for yy,label,color,(marker,style) in zip(errors,
        ['Leading','One correction','Two corrections'],colors,styles):
    axes[1].loglog(xx,yy,style,marker=marker,color=color,markersize=4,label=label)
axes[1].set(title='Joint log-gamma transition',xlabel='Reflected exponent $m$',
            ylabel='Relative error in the moment')
axes[1].legend(frameon=False,loc='lower left')
for ax in axes:
    ax.grid(True,which='major',color='#d9dee4',linewidth=.55)
    ax.set_axisbelow(True)
out=ROOT/'figures'
out.mkdir(exist_ok=True)
fig.savefig(out/'correction_diagnostics.pdf',metadata={'Title':'Asymptotic correction diagnostics'})
fig.savefig(out/'correction_diagnostics.png',dpi=200)
print('Wrote diagnostic figure as vector PDF and 200-dpi PNG.')
