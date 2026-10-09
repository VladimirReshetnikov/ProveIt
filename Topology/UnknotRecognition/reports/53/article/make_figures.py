"""Build exact article tables and scientific figures from archived raw timings."""

import argparse
import csv
import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.ticker import ScalarFormatter


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--results', type=Path)
    parser.add_argument('--output-dir', type=Path)
    args = parser.parse_args()
    source_here = Path(__file__).resolve().parent
    here = args.output_dir or source_here
    here.mkdir(parents=True, exist_ok=True)
    results = args.results or source_here.parent/'results'
    records = json.loads((results/'normal_benchmark.json').read_text())['records']
    figures, tables = here/'figures', here/'tables'
    figures.mkdir(exist_ok=True)
    tables.mkdir(exist_ok=True)
    dim = [r for r in records if r['kind'] == 'dimension']
    core = [r for r in records if r['kind'] == 'core']

    rows = [r'\begin{tabular}{rrrrrr}', r'\toprule',
            r'$t$ & Input bits & Three weights (ms) & $7t$ weights (ms) & Paired ratio & A/A \\',
            r'\midrule']
    for r in dim:
        m, p = r['medians'], r['paired_median_ratios']
        rows.append(f"{r['tetrahedra']} & {r['input_coordinate_bits']} & "
                    f"{m['three_weights']['total']*1000:.2f} & "
                    f"{m['full_coordinates']['total']*1000:.2f} & "
                    f"{p['full_coordinates/three_weights']:.2f} & "
                    f"{p['three_weights/three_weights_control']:.3f}" + r' \\')
    rows += [r'\bottomrule', r'\end{tabular}']
    (tables/'normal_dimension.tex').write_text('\n'.join(rows)+'\n')

    rows = [r'\begin{tabular}{rrrrrr}', r'\toprule',
            r'$b$ & Input bits & Direct (ms) & Core (ms) & Paired ratio & A/A \\',
            r'\midrule']
    for r in core:
        m, p = r['medians'], r['paired_median_ratios']
        rows.append(f"{r['parameter']:,} & {r['input_coordinate_bits']:,} & "
                    f"{m['three_weights']['total']*1000:.2f} & "
                    f"{m['core']['total']*1000:.2f} & "
                    f"{p['three_weights/core']:.2f} & "
                    f"{p['core/core_control']:.3f}" + r' \\')
    rows += [r'\bottomrule', r'\end{tabular}']
    (tables/'normal_core.tex').write_text('\n'.join(rows)+'\n')

    plt.rcParams.update({'font.family':'DejaVu Sans', 'font.size':9,
                         'axes.spines.top':False, 'axes.spines.right':False,
                         'axes.labelcolor':'#17324D', 'text.color':'#17324D',
                         'axes.edgecolor':'#9BA9B6', 'savefig.facecolor':'white',
                         'pdf.fonttype':42, 'ps.fonttype':42})
    fig, axes = plt.subplots(1, 2, figsize=(6.7, 3.6), constrained_layout=True)
    configurations = [
        (axes[0], dim, [('full_coordinates','Full coordinates','#AA6144'),
                       ('three_weights','Three weights','#087E8B')],
         'A  Component statistics', 'Tetrahedra'),
        (axes[1], core, [('three_weights','Direct query','#AA6144'),
                        ('core','Reduced disc count','#087E8B')],
         'B  Remove multiplicity', r'Exponent $b$ in $g=2^b$'),
    ]
    for ax, subset, arms, title, xlabel in configurations:
        xs = [r['parameter'] for r in subset]
        for arm, label, color in arms:
            mid = [r['medians'][arm]['total']*1000 for r in subset]
            lows = [min(s['timings'][arm]['total']*1000 for s in r['samples']) for r in subset]
            highs = [max(s['timings'][arm]['total']*1000 for s in r['samples']) for r in subset]
            ax.fill_between(xs, lows, highs, color=color, alpha=0.10, linewidth=0)
            ax.plot(xs, mid, marker='o', markersize=4, color=color, linewidth=1.7, label=label)
        ax.set_xscale('log', base=2)
        ax.set_yscale('log')
        ax.set_xticks(xs)
        ax.xaxis.set_major_formatter(ScalarFormatter())
        ax.set_title(title, loc='left', fontweight='bold', pad=12, fontsize=10)
        ax.set_xlabel(xlabel)
        ax.set_ylabel('Checked time (ms)')
        ax.grid(axis='y', which='major', alpha=0.2)
        ax.legend(loc='upper left', frameon=False, fontsize=8)
    for suffix in ('pdf','png'):
        fig.savefig(figures/f'normal_query_benchmarks.{suffix}', dpi=220)
    plt.close(fig)

    with (tables/'normal_benchmark_summary.csv').open('w',newline='') as f:
        out=csv.writer(f)
        out.writerow(['kind','parameter','tetrahedra','input_bits','arm',
                      'median_produce_ms','median_verify_ms','median_total_ms',
                      'certificate_bytes','orbit_cycles','maximum_weight_runs'])
        for r in records:
            for arm,m in r['medians'].items():
                meta=r['metadata'][arm]
                out.writerow([r['kind'],r['parameter'],r['tetrahedra'],
                              r['input_coordinate_bits'],arm,m['produce']*1000,
                              m['verify']*1000,m['total']*1000,meta['certificate_bytes'],
                              meta['stats']['orbit_cycles'],meta['stats']['maximum_weight_runs']])
    largest=dim[-1]
    total_discs=sum(sum(row) for row in largest['coordinates'])
    print(json.dumps({'figure':str(figures/'normal_query_benchmarks.pdf'),
                      'largest_dimension_case_normal_discs':total_discs,
                      'largest_dimension_case_normal_discs_scientific':f'{total_discs:.5e}'}))


if __name__ == '__main__':
    main()
