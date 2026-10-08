"""Generate article tables and exact-data figures from the archived JSON.

Run from any directory: python3 render_results.py
This script does not rerun measurements. Matplotlib is needed for figures.
"""
from pathlib import Path
import json
import math

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.ticker import ScalarFormatter

HERE = Path(__file__).resolve().parent
FAST = HERE.parents[1] / 'fast'
TABLES = HERE / 'tables'
FIGURES = HERE / 'figures'
TABLES.mkdir(exist_ok=True)
FIGURES.mkdir(exist_ok=True)


def read(name):
    return json.loads((FAST / name).read_text())


def escape(value):
    return str(value).replace('_', r'\_').replace('&', r'\&')


def table(name, label, caption, columns, headers, rows, note=''):
    lines = [r'\begin{table}[htbp]', r'\centering\small',
             r'\setlength{\tabcolsep}{4pt}',
             r'\begin{tabular}{@{}' + columns + r'@{}}', r'\toprule',
             ' & '.join(headers) + r'\\\midrule']
    lines.extend(' & '.join(str(x) for x in row) + r'\\' for row in rows)
    lines.extend([r'\bottomrule', r'\end{tabular}',
                  r'\caption{' + caption + (' ' + note if note else '') + '}',
                  r'\label{' + label + '}', r'\end{table}', ''])
    (TABLES / name).write_text('\n'.join(lines))


def ms(value):
    return f'{1000 * value:.3f}'


def ratio(value):
    return f'{value:.3f}'


def sci_integer(value):
    if value < 1000000:
        return f'{value:,}'.replace(',', r'\,')
    power = len(str(value)) - 1
    return rf'${value / 10 ** power:.4f}\cdot10^{{{power}}}$'


interval = read('interval_research/results.json')
normal = read('normal_orbit_research/results.json')
scalar = read('coefficient_research/results.json')
overlap = read('cyclic_overlap_research/results.json')

chains = {}
for row in interval['rows']:
    if row['family'] == 'adjacent_periodic_chain':
        chains.setdefault(row['k'], {})[row['rule']] = row
table('interval.tex', 'tab:interval',
      'Adjacent periodic interval family. Times are medians in milliseconds.',
      'rrrrrr', ['$k$', 'Old cycles', 'Sharp cycles', 'Old ms', 'Sharp ms', 'Ratio'],
      [[k, arms['aht']['cycles'], arms['fine_wilf']['cycles'],
        ms(arms['aht']['seconds_median']), ms(arms['fine_wilf']['seconds_median']),
        f"{arms['aht']['seconds_median'] / arms['fine_wilf']['seconds_median']:.1f}"]
       for k, arms in sorted(chains.items())],
      'This ratio uses the two medians; it is not a paired statistic.')

table('normal.tex', 'tab:normal',
      'Layered meridian topology, with no expanded surface construction.',
      'rrrrr', ['$t$', 'Normal discs $W$', 'Max. coordinate bits', 'Total cycles', 'Time ms'],
      [[c['tetrahedra'], sci_integer(c['result']['normal_disks']),
        c['result']['maximum_coordinate_bits'], c['result']['cycles'],
        ms(c['medians']['fine_wilf'])] for c in normal['cases']],
      'Large disc counts are rounded here; exact integers are stored in the JSON.')

sparse = [r for r in scalar['algebraic'] if r['dot_variables'] == 2]
dense = [r for r in scalar['algebraic'] if r['dot_variables'] > 2]
table('scalar_sparse.tex', 'tab:sparse',
      'Sparse two-field algebraic family: complete compression-pass medians.',
      'rrrrrrr', ['$d$', 'Objects', 'Direct ms', 'Span ms', 'Forest ms',
                  'Direct/forest', 'A/A'],
      [[r['degree'], r['objects'],
        *[ms(r['compression']['median_seconds'][a]) for a in ('direct', 'span', 'forest')],
        ratio(r['compression']['median_paired_ratios']['direct/forest']),
        ratio(r['compression']['median_paired_ratios']['direct/control'])] for r in sparse])

table('scalar_dense.tex', 'tab:dense',
      'Dense homogeneous coefficients: equations and complete compression timings.',
      'rrrrrrr', ['$b$', 'Direct equations', 'Span equations', 'Direct ms',
                  'Span ms', 'Direct/span', 'A/A'],
      [[r['dot_variables'], r['solve']['facts']['direct']['equations'],
        r['solve']['facts']['span']['equations'],
        *[ms(r['compression']['median_seconds'][a]) for a in ('direct', 'span')],
        ratio(r['compression']['median_paired_ratios']['direct/span']),
        ratio(r['compression']['median_paired_ratios']['direct/control'])] for r in dense],
      'Every row has 128 original variables; the forest has 64 variables and 64 equations.')

names = {'conway': 'Conway', 'kinoshita_terasaka': 'Kinoshita--Terasaka',
         'hard_unknot_8': 'Hard unknot (8)', 'stress_braid5_36': '5-braid stress (36)',
         'torus_3_5': '$T(3,5)$'}
rows = []
for r in scalar['knots']:
    if 'prefix_solves' not in r:
        continue
    f = r['prefix_solves']['facts']
    rows.append([names[r['name']], r['eligible_prefix_solves'],
        sum(x['equations'] for x in f['direct']),
        sum(x['equations'] for x in f['span']),
        sum(x['equations'] for x in f['forest']),
        sum(x['variables'] for x in f['direct']),
        sum(x['stats']['reduced_variables'] for x in f['forest'])])
table('scalar_natural_counts.tex', 'tab:natural_counts',
      'Actual prefix commutants: sums of per-solve counts, not one simultaneous system.',
      'lrrrrrr', ['Input', 'Solves', 'Direct eq.', 'Span eq.', 'Forest eq.', '$V$', '$V_F$'], rows)

table('scalar_scans.tex', 'tab:scans',
      'Complete raw homology scans with identical scan order and graded answer.',
      'lrrrrrr', ['Input', 'Direct ms', 'Span ms', 'Forest ms', 'D/span', 'D/forest', 'A/A'],
      [[names[r['name']],
        *[ms(r['raw_scan']['median_seconds'][a]) for a in ('direct', 'span', 'forest')],
        *[ratio(r['raw_scan']['median_paired_ratios'][a]) for a in
          ('direct/span', 'direct/forest', 'direct/control')]] for r in scalar['knots']],
      'Ratios are median paired ratios. Values near one should be read alongside the A/A control.')

gordian = next(r for r in overlap['rows'] if r['name'] == 'gordian')
table('overlap_gordian.tex', 'tab:gordian',
      'Complete configured Gordian recognition queries, including independent replay.',
      'lrrrrrr', ['Search mode', 'Pairwise ms', 'Adaptive ms', 'Joint ms',
                  'P/adaptive', 'P/joint', 'A/A'],
      [[escape(mode),
        *[ms(r['completed_median_seconds'][a]) for a in ('pairwise', 'adaptive', 'joint')],
        *[ratio(r['paired_ratios'][a]['median']) for a in
          ('pairwise/adaptive', 'pairwise/joint', 'pairwise/control')]]
       for mode, r in gordian['modes'].items()],
      'The explicit-query replacement can also be reached inside the configured compressed route.')

knames = {'gordian-derived': 'Gordian residual', 'random-8x64': r'$8\times64$ random',
          'random-32x64': r'$32\times64$ random', 'random-128x64': r'$128\times64$ random',
          'duplicate-periodic': 'Periodic duplicates'}
table('overlap_kernels.tex', 'tab:overlap_kernels',
      'Exact explicit overlap queries, including all index construction and any failed prelude.',
      'lrrrrrr', ['Input', r'$\ell$', 'Gain', 'Pairwise ms', 'Adaptive ms', 'Joint ms', 'P/adaptive'],
      [[knames[r['name']], r['total_length'], r['expected_gain'],
        *[ms(r['completed_median_seconds'][a]) for a in ('pairwise', 'adaptive', 'joint')],
        ratio(r['paired_ratios']['pairwise/adaptive']['median'])] for r in overlap['kernels']],
      'Only the first row comes from the measured knot presentation; the others are synthetic capacity cases.')

whole_rows = []
for r in overlap['rows']:
    ex, co = r['modes']['explicit'], r['modes']['compressed']
    whole_rows.append([escape(r['name']), r['crossings'],
        ms(ex['completed_median_seconds']['pairwise']),
        ms(ex['completed_median_seconds']['adaptive']),
        ratio(ex['paired_ratios']['pairwise/adaptive']['median']),
        ms(co['completed_median_seconds']['pairwise']),
        ms(co['completed_median_seconds']['adaptive']),
        ratio(co['paired_ratios']['pairwise/adaptive']['median'])])
table('overlap_corpus.tex', 'tab:corpus',
      'All whole-query cases. E and C denote the explicit and compressed configurations.',
      'lrrrrrrr', ['Case', '$n$', 'E pair ms', 'E adapt ms', 'E ratio',
                  'C pair ms', 'C adapt ms', 'C ratio'], whole_rows,
      'All statuses are complete and agree with the listed corpus expectations in the raw data.')

plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 8,
    'axes.titlesize': 9, 'axes.labelsize': 8, 'legend.fontsize': 7,
    'xtick.labelsize': 7, 'ytick.labelsize': 7, 'axes.spines.top': False,
    'axes.spines.right': False, 'pdf.fonttype': 42, 'savefig.bbox': 'tight'})
colors = {'direct': '#9A542C', 'aht': '#9A542C', 'span': '#226D91',
          'fine_wilf': '#226D91', 'forest': '#23806C', 'fine_wilf_AA': '#999999'}
fig, axes = plt.subplots(1, 2, figsize=(6.30, 2.95), layout='constrained')
for rule, label in [('aht', 'Original merger'), ('fine_wilf', 'Sharp merger')]:
    axes[0].plot(list(chains), [1000 * x[rule]['seconds_median'] for x in chains.values()],
                 marker='o', lw=1.4, ms=3, color=colors[rule], label=label)
axes[0].set(xlabel='Pairings k', ylabel='Count time (ms; log scale)', yscale='log',
            title='Adjacent periodic regions')
axes[0].set_xticks([8, 32, 64, 128])
for arm, label in [('aht', 'Original merger'), ('fine_wilf', 'Sharp merger'),
                   ('fine_wilf_AA', 'Sharp A/A')]:
    axes[1].plot([c['tetrahedra'] for c in normal['cases']],
                 [1000 * c['medians'][arm] for c in normal['cases']], marker='o',
                 lw=1.3, ms=3, color=colors[arm], label=label,
                 linestyle='--' if arm.endswith('AA') else '-')
axes[1].set(xlabel='Tetrahedra t', ylabel='Topology time (ms; log scale)',
            yscale='log', title='Binary normal meridians')
axes[1].set_xticks([4, 32, 64, 128])
for ax in axes:
    ax.grid(axis='y', alpha=.16)
    ax.legend(frameon=False, loc='upper left')
fig.savefig(FIGURES / 'interval_normal.pdf')
fig.savefig(FIGURES / 'interval_normal.png', dpi=220)
plt.close(fig)

fig, axes = plt.subplots(1, 2, figsize=(6.30, 2.95), layout='constrained')
for arm, label in [('direct', 'Direct'), ('span', 'Coefficient span'), ('forest', 'Span + forest')]:
    xs = [r['dot_variables'] for r in dense]
    axes[0].plot(xs, [r['solve']['facts'][arm]['equations'] for r in dense],
                 marker='o', lw=1.5, ms=3, color=colors[arm], label=label)
    axes[1].plot(xs, [1000 * r['compression']['median_seconds'][arm] for r in dense],
                 marker='o', lw=1.5, ms=3, color=colors[arm], label=label)
axes[0].set(ylabel='Generated equations (log scale)', title='Remove coefficient dependence',
            yscale='log')
axes[1].set(ylabel='Compression time (ms; log scale)', title='Include the full compression pass',
            yscale='log')
for ax in axes:
    ax.set_xlabel('Dot variables b')
    ax.set_xticks([8, 10, 12])
    ax.grid(axis='y', alpha=.16)
    ax.legend(frameon=False, loc='upper left')
fig.savefig(FIGURES / 'scalar_coefficients.pdf')
fig.savefig(FIGURES / 'scalar_coefficients.png', dpi=220)
plt.close(fig)
print(f'Generated {len(list(TABLES.glob("*.tex")))} tables and 2 figures.')
