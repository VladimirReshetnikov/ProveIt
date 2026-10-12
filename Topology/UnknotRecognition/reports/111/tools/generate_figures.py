"""Rebuild the article's exact-count vector figure and descriptive timing table."""
import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]


def main():
    article = ROOT/'article'
    figures = article/'figures'
    figures.mkdir(parents=True, exist_ok=True)
    audit = json.loads((ROOT/'results/native_audit.json').read_text())
    counts = audit['counts']
    plt.rcParams.update({'font.family':'DejaVu Sans', 'font.size':10,
                         'axes.spines.top':False, 'axes.spines.right':False,
                         'pdf.fonttype':42, 'axes.titleweight':'bold'})
    fig, (ax, bx) = plt.subplots(1, 2, figsize=(10.6, 3.8), gridspec_kw={'width_ratios':[1.22, 1]})
    labels = ['Current canonical', 'Group terminal alone', 'Canonical + group',
              'Deferred forests', 'Deferred + group']
    fields = ['canonical', 'group', 'canonical_plus_group', 'deferred', 'deferred_plus_group']
    values = [counts[x+'/COMPLETE'] for x in fields]
    colors = ['#79919E', '#41677A', '#2E7180', '#79919E', '#1B606D']
    ax.barh(range(len(labels)), values, color=colors, height=.57)
    ax.set_yticks(range(len(labels)), labels)
    ax.invert_yaxis()
    ax.set_xlim(0, 128)
    ax.set_xticks([0, 30, 60, 90, 120])
    ax.set_xlabel('Certified cases out of 120')
    ax.set_title('Whole-cut certificates', loc='left', pad=13)
    ax.xaxis.grid(True, color='#D9E0E4', linewidth=.6)
    ax.set_axisbelow(True)
    ax.spines['left'].set_visible(False)
    ax.tick_params(axis='y', length=0, pad=7)
    for i, value in enumerate(values):
        ax.text(value+1.4, i, str(value), va='center', fontsize=10, fontweight='bold')
    bx.plot(range(6), [18,16,13,7,3,0], color='#1B606D', marker='o', linewidth=2,
            label='Production trace')
    bx.plot(range(6), [18,16,14,11,5,0], color='#B3883E', marker='s', linestyle='--',
            linewidth=1.6, markersize=4.5, label='Displayed hand reduction')
    bx.set_title('Figure-eight component of genus two', loc='left', pad=13, fontsize=10.5)
    bx.set_xlabel('Completed Tietze pivots')
    bx.set_ylabel('Total cyclically reduced relator length')
    bx.set_xticks(range(6))
    bx.set_yticks([0, 3, 6, 9, 12, 15, 18])
    bx.set_ylim(-.5, 19.5)
    bx.grid(True, color='#D9E0E4', linewidth=.6)
    bx.legend(loc='upper right', bbox_to_anchor=(1, .75), frameon=False, fontsize=8.5)
    fig.tight_layout(w_pad=2.7)
    fig.savefig(figures/'coverage_and_trace.pdf', bbox_inches='tight')
    fig.savefig(figures/'coverage_and_trace.png', dpi=180, bbox_inches='tight')
    plt.close(fig)

    raw = json.loads((ROOT/'results/terminal_benchmarks.json').read_text())
    cases = {x['id']:x for x in raw['cases']}
    retry_path = ROOT/'results/pachner_benchmark_retry.json'
    retry = json.loads(retry_path.read_text()) if retry_path.exists() else None
    if retry and 'arms' in retry:
        cases[retry['id']] = retry
    entries = [
        ('pilot/finite_trefoil/0', 'Trefoil cut'),
        ('pilot/finite_figureEight/0', 'Figure-eight cut'),
        ('pachner23_5_8_2/mixed', 'Mixed Pachner cut'),
        ('meridian_copies/1', 'One meridian copy'),
        ('meridian_copies/64', '64 meridian copies'),
        ('meridian_copies/1024', '1024 meridian copies'),
        ('meridian_binary/128', r'$2^{128}$ copies'),
        ('meridian_binary/500', r'$2^{500}$ copies'),
        ('meridian_binary/16384', r'$2^{16384}$ copies'),
    ]
    lines = [r'\begin{table}[htbp]', r'\centering\small',
             r'\begin{tabular}{lrrrr}', r'\toprule',
             r'Case & Group ms & Portfolio ms & Regina ms & Literal tets \\', r'\midrule']
    summary = []
    for identifier, label in entries:
        row = cases[identifier]
        if 'arms' not in row:
            lines.append(label + r' & \multicolumn{4}{c}{Aggregate case timeout} \\')
            continue
        arms = row['arms']
        g = arms['group_A']['median_seconds']
        b = arms['group_B']['median_seconds']
        portfolio = arms['portfolio']['median_seconds']
        oracle = arms.get('regina')
        fmt = lambda x: f'{x*1000:.2f}'
        lines.append(f'{label} & {fmt(g)} & {fmt(portfolio)} & '
                     + (fmt(oracle['median_seconds']) if oracle else r'---')
                     + ' & ' + (str(oracle['literal_tetrahedra']) if oracle else r'---') + r' \\')
        summary.append(dict(id=identifier, group_median_seconds=g, group_B_median_seconds=b,
                            aa_median_ratio=g/b, portfolio_median_seconds=portfolio,
                            regina_median_seconds=oracle['median_seconds'] if oracle else None,
                            regina_over_group=oracle['median_seconds']/g if oracle else None))
    lines += [r'\bottomrule', r'\end{tabular}',
              r'\caption{Median complete-query costs in milliseconds, seven rounds. Group uses arm A; the two identical A/A arms are retained in the raw data. Dashes denote the expansion cap. The mixed Pachner row is from the separately retained completed retry.}',
              r'\label{tab:timings}', r'\end{table}']
    (article/'sections/benchmark_table.tex').write_text('\n'.join(lines)+'\n')
    (ROOT/'results/benchmark_summary.json').write_text(json.dumps(dict(
        timing_claim='Descriptive local complete-query observations, not asymptotic estimates.',
        sources=['terminal_benchmarks.json','pachner_benchmark_retry.json'],
        note='Original mixed-case aggregate 45-second timeout is preserved in terminal_benchmarks.json.',
        cases=summary), indent=2)+'\n')


if __name__ == '__main__':
    main()
