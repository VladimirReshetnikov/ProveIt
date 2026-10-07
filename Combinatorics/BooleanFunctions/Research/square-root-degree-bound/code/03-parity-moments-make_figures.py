#!/usr/bin/env python3
"""Regenerate the article's scientific figure and rounded table fragments.

Requires numpy and matplotlib. Exact input data come from verify.py.
"""
from pathlib import Path
import json
import math

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
plt.rcParams.update({
    'font.family': 'DejaVu Sans', 'font.size': 9,
    'axes.titlesize': 9.5, 'axes.labelsize': 9,
    'legend.fontsize': 8.5, 'axes.spines.top': False,
    'axes.spines.right': False, 'pdf.fonttype': 42,
    'savefig.bbox': 'tight',
})
BLUE, ORANGE, GREY = '#204e73', '#b45619', '#66737d'


def profile_figure():
    fig, axs = plt.subplots(1, 2, figsize=(6.5, 3.3), layout='constrained')
    mu = np.linspace(0, 2, 1601)
    u = mu - np.floor(mu)
    h = np.abs(u - 0.5)
    values = 0.75 + h - h*h
    ax = axs[0]
    ax.plot(mu, values, lw=2.2, color=BLUE, label=r'$B(\mu)$, $k\geq3$')
    ax.scatter([0.5, 1.5], [0.75, 0.75], s=65, zorder=5,
               facecolor='white', edgecolor=ORANGE, linewidth=1.8,
               label=r'No minimizer for $k=4$')
    ax.set(xlabel=r'Mean $\mu$', ylabel='Variance infimum',
           title='A. Prescribed-mean profile',
           xlim=(-0.025, 2.025), ylim=(0.735, 1.025))
    ax.set_xticks([0, 0.5, 1, 1.5, 2])
    ax.set_yticks([0.75, 0.875, 1])
    ax.grid(alpha=0.16)
    ax.legend(loc='upper center', bbox_to_anchor=(0.5, -0.22), frameon=False)

    distance = np.geomspace(0.001, 0.5, 5000)
    depth = 2*np.ceil((1.5+distance)/(4*distance))
    ax = axs[1]
    ax.loglog(distance, depth, color=BLUE, lw=1.8, label=r'Exact depth $2a_{\min}$')
    ax.loglog(distance, 3/(4*distance), '--', color=ORANGE, lw=1.5,
              label=r'Asymptotic $3/(4h)$')
    ax.set(xlabel='Distance $h=1/2-u$\nfrom a half-integer mean',
           ylabel='Minimum negative depth',
           title='B. Order-four support depth',
           xlim=(0.0009, 0.56), ylim=(1.4, 1000))
    ax.grid(which='major', alpha=0.16)
    ax.legend(loc='upper center', bbox_to_anchor=(0.5, -0.22), frameon=False)
    dest = ROOT/'figures'
    dest.mkdir(exist_ok=True)
    fig.savefig(dest/'profile_and_support.pdf')
    fig.savefig(dest/'profile_and_support.png', dpi=180)
    plt.close(fig)


def scientific_tex(value):
    value = abs(float(value))
    mantissa, exp = f'{value:.2e}'.split('e')
    return rf'${mantissa}\times10^{{{int(exp)}}}$'


def tables():
    data = json.loads((ROOT/'data'/'verification_results.json').read_text())
    indexed = {(v['k'], v['R']): v for v in data['exact_affine_families']['rows']}
    rows = []
    for k in (4, 6, 10, 18):
        vals = [f"{indexed[k, r]['variance_decimal']:.9f}" for r in (18, 32, 100, 1000)]
        rows.append(str(k)+' & '+' & '.join(vals)+r'\\')
    table = (r'\begin{tabular}{@{}rcccc@{}}'+'\n'+r'\toprule'+'\n'
             +r'Order $k$ & $R=18$ & $R=32$ & $R=100$ & $R=1000$\\'+'\n'
             +r'\midrule'+'\n'+'\n'.join(rows)+'\n'
             +r'\bottomrule'+'\n'+r'\end{tabular}'+'\n')
    (ROOT/'data'/'finite_variance_table.tex').write_text(table)
    if 'numerical_diagnostics' in data:
        rows = []
        for row in data['numerical_diagnostics']['moment_expansion']:
            if row['s'] not in ('8.0', '12.0', '20.0', '30.0', '20.5'):
                continue
            s = row['s'].removesuffix('.0')
            vals = [scientific_tex(v) for v in row['relative_errors_orders_0_to_3']]
            rows.append(s+' & '+' & '.join(vals)+r'\\')
        table = (r'\begin{tabular}{@{}rcccc@{}}'+'\n'+r'\toprule'+'\n'
                 +r'$s$ & $J=0$ & $J=1$ & $J=2$ & $J=3$\\'+'\n'
                 +r'\midrule'+'\n'+'\n'.join(rows)+'\n'
                 +r'\bottomrule'+'\n'+r'\end{tabular}'+'\n')
        (ROOT/'data'/'mellin_errors_table.tex').write_text(table)


if __name__ == '__main__':
    profile_figure()
    tables()
    print('Regenerated profile_and_support.pdf/.png and table fragments.')
