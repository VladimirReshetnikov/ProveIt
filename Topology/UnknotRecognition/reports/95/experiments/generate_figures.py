"""Generate the article's exact-count figure from preserved measurements."""

import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.ticker import ScalarFormatter


ROOT = Path(__file__).resolve().parents[1]


def main():
    data = json.loads((ROOT / 'results/column_peeling_benchmark.json').read_text())
    rows = [r for r in data['records'] if r['family'] == 'rectangular_chain']
    rows.sort(key=lambda r: r['rows'])
    m = [r['rows'] for r in rows]
    old = [r['baseline_stats']['entry_scans'] for r in rows]
    new = [r['new_stats']['source_entries'] + r['new_stats']['removal_incidence_visits']
           for r in rows]
    audit = json.loads((ROOT / 'data/native_audit.json').read_text())
    assert audit['counts']['baseline_COMPLETE'] == 78
    assert audit['counts']['COMPLETE'] == 85

    plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 9,
                         'axes.spines.top': False, 'axes.spines.right': False,
                         'axes.labelcolor': '#18354D', 'text.color': '#18354D',
                         'axes.titleweight': 'bold', 'svg.fonttype': 'none'})
    fig, axes = plt.subplots(1, 2, figsize=(10.2, 3.8),
                             gridspec_kw={'width_ratios': [1, 1.05]})
    ax = axes[0]
    ax.plot(m, old, 'o-', color='#B96833', lw=2, ms=5, label='Pinned planner')
    ax.plot(m, new, 's-', color='#146B75', lw=2, ms=5, label='Column peeling')
    ax.set_xscale('log', base=2)
    ax.set_yscale('log', base=10)
    ax.set_xticks(m, [str(x) for x in m])
    ax.set_ylim(70, 1.0e6)
    ax.set_xlabel('Task rows m (rectangular chain)')
    ax.set_ylabel('Recorded incidence visits')
    ax.set_title('A. Exact planner work', loc='left', pad=12)
    ax.grid(axis='y', alpha=.2)
    ax.legend(frameon=False, loc='upper left', fontsize=8)

    ax = axes[1]
    parts = [('Certified census', [78, 85], '#146B75'),
             ('Annular refusal', [11, 0], '#D69A55'),
             ('Raw obstruction', [7, 11], '#AB5650'),
             ('Three-handles', [10, 10], '#89969D')]
    left = [0, 0]
    for name, values, color in parts:
        ax.barh([1, 0], values, left=left, color=color, height=.47, label=name)
        for y, width, start in zip([1, 0], values, left):
            if width:
                ax.text(start + width / 2, y, str(width), ha='center', va='center',
                        color='white', fontsize=8, fontweight='bold')
        left = [x + y for x, y in zip(left, values)]
    ax.set_yticks([1, 0], ['Pinned', 'Extended'])
    ax.set_xlim(0, 106)
    ax.set_ylim(-.55, 1.6)
    ax.set_xticks([0, 25, 50, 75, 106])
    ax.set_xlabel('Same 106 supplied normal cuts')
    ax.set_title('B. Native census coverage', loc='left', pad=12)
    ax.legend(frameon=False, loc='upper center', bbox_to_anchor=(.5, -.28),
              ncol=2, fontsize=8)
    ax.spines['left'].set_visible(False)
    ax.tick_params(axis='y', length=0)
    fig.subplots_adjust(left=.08, right=.98, top=.86, bottom=.26, wspace=.38)
    out = ROOT / 'article/figures'
    out.mkdir(exist_ok=True)
    fig.savefig(out / 'work_and_coverage.png', dpi=300, facecolor='white')
    fig.savefig(out / 'work_and_coverage.svg', facecolor='white')
    plt.close(fig)


if __name__ == '__main__':
    main()
