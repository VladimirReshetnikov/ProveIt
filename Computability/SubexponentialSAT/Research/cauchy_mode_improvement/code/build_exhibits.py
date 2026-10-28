#!/usr/bin/env python3
"""Build report tables and a static figure from the supplied exact result files.

The figure requires matplotlib. These are enumeration counts, not SAT timings.
The kernel and arithmetic checks have no third-party dependency.
"""
from pathlib import Path
import json
import math
import os
import tempfile


def main():
    root = Path(__file__).resolve().parents[1]
    results = root / 'results'
    data = json.loads((results / 'mode_counts.json').read_text())
    verification = json.loads((results / 'verification.json').read_text())
    counts = verification['counts']
    labels = [
        ('Exact rational kernel identities', 'exact_rational_kernel_identities'),
        ('Exact rational target valuations', 'exact_rational_target_valuations'),
        ('Scalar modular truncated identities', 'scalar_modular_truncated_identities'),
        ('Actual extension target valuations', 'actual_extension_target_valuations'),
        ('Actual deformation-to-kernel checks', 'actual_deformation_to_kernel_checks'),
        ('Actual extension truncated identities', 'actual_extension_truncated_identities'),
        ('Affine product assignment checks', 'affine_product_assignment_checks'),
        ('Complete tiny deformed contractions', 'complete_tiny_contraction_checks'),
    ]
    lines = [r'\begin{center}', r'\begin{tabular}{@{}lr@{}}',
             r'\toprule', r'Executed check & Number passed\\', r'\midrule']
    for label, key in labels:
        lines.append(f'{label} & {counts[key]:,}'+r'\\')
    lines += [r'\bottomrule', r'\end{tabular}', r'\end{center}',
              r'The invalid-domain regression and nonunit-inversion rejection checks also passed.']
    (results / 'validation_summary.tex').write_text('\n'.join(lines)+'\n')
    index = {(r['precision'], r['colors'], r['scheme']):r for r in data['rows']}
    lines = [r'\begin{center}', r'\small',
             r'\begin{tabular}{@{}rrrrrr@{}}', r'\toprule',
             r'$p$ & $c$ & $\log_2 N_1$ & $\log_2 N_2$ & $\log_2 N_3$ & $\log N_3/\log N_1$\\',
             r'\midrule']
    for c in (1,4):
        for p in (64,256,1024,4096):
            rows = [index[p,c,s] for s in ('geometric','newton','skeleton')]
            lines.append(f'{p} & {c} & '+ ' & '.join(f"{r['log2_count']:.3f}" for r in rows)+
                         f" & {rows[-1]['log2_ratio_to_geometric']:.4f}"+r'\\')
        if c == 1: lines.append(r'\addlinespace')
    lines += [r'\bottomrule',r'\end{tabular}',r'\end{center}',
              r'Here $N_1,N_2,N_3$ denote geometric, Newton, and factorial Cauchy abstract counts, respectively. All integer counts are stored in the accompanying CSV and JSON files.']
    (results / 'mode_table.tex').write_text('\n'.join(lines)+'\n')
    os.environ.setdefault('MPLCONFIGDIR', str(Path(tempfile.gettempdir())/'cauchy_modes_matplotlib'))
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,
                         'axes.spines.top':False,'axes.spines.right':False,
                         'pdf.fonttype':42})
    fig, ax = plt.subplots(figsize=(8.2,4.4), layout='constrained')
    palette = {'newton':'#1d667b','skeleton':'#b34c2a'}
    for c, style in ((1,'-'),(4,'--')):
        for scheme in ('newton','skeleton'):
            series = [r for r in data['rows'] if r['colors']==c and r['scheme']==scheme]
            ax.plot([r['precision'] for r in series],
                    [r['log2_ratio_to_geometric'] for r in series],
                    linestyle=style, marker='o' if c==1 else 's',
                    markersize=4,color=palette[scheme],
                    label=f"{'Cauchy' if scheme=='skeleton' else 'Newton'}, {c} {'family' if c==1 else 'families'}")
    ax.axhline(1/math.sqrt(2),color=palette['newton'],alpha=.55,linewidth=1,linestyle=':')
    ax.axhline(1/math.sqrt(3),color=palette['skeleton'],alpha=.55,linewidth=1,linestyle=':')
    ax.set_xscale('log',base=2)
    ps=data['precisions'];ax.set_xticks(ps,[str(p) for p in ps])
    ax.set_xlabel('Precision budget p (total mode weight < p)')
    ax.set_ylabel('Logarithm of count / geometric logarithm')
    ax.set_ylim(.54,.97)
    ax.grid(True,alpha=.17)
    ax.legend(frameon=False,loc='upper right',ncols=2,fontsize=8.5)
    ax.text(35,1/math.sqrt(2)+.009,r'$1/\sqrt{2}$',color=palette['newton'])
    ax.text(35,1/math.sqrt(3)+.009,r'$1/\sqrt{3}$',color=palette['skeleton'])
    ax.set_title('Exact abstract mode counts: smaller exponential work',loc='left',pad=14)
    figures=root/'figures';figures.mkdir(exist_ok=True)
    fig.savefig(figures/'mode_entropy.pdf')
    fig.savefig(figures/'mode_entropy.png',dpi=180)
    plt.close(fig)
    print('Generated report tables and mode_entropy.pdf/.png from exact results.')


if __name__=='__main__': main()
