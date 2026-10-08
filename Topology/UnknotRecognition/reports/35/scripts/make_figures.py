#!/usr/bin/env python3
"""Regenerate every numerical table and the static figure from retained evidence."""
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'article' / 'generated'
OUT.mkdir(parents=True, exist_ok=True)
ALG = json.loads((ROOT / 'evidence/primary_split_20261008.json').read_text())
GEO = json.loads((ROOT / 'evidence/surface_gluing_20261008.json').read_text())


def table(name, caption, label, columns, headers, rows):
    lines = [r'\begin{table}[!htbp]', r'\centering\small',
             r'\setlength{\tabcolsep}{4pt}',
             r'\caption{' + caption + '}', r'\label{' + label + '}',
             r'\begin{tabular}{' + columns + '}', r'\toprule',
             ' & '.join(headers) + r'\\', r'\midrule']
    lines += [' & '.join(map(str, row)) + r'\\' for row in rows]
    lines += [r'\bottomrule', r'\end{tabular}', r'\end{table}', '']
    (OUT / name).write_text('\n'.join(lines))

names = {'conway': 'Conway', 'kinoshita_terasaka': 'Kinoshita--Terasaka',
         'hard_unknot_8': 'Hard unknot', 'stress_braid5_36': 'Stress braid',
         'torus_3_5': '$T(3,5)$'}
rows = []
for x in ALG['knots']:
    ratio = x['timing']['median_fitting_over']
    stats = x['stats']['primary']
    rows.append([names[x['name']], x['crossings'], f"{ratio['primary']:.3f}",
                 f"{ratio['control']:.3f}", stats['fitting_primary_candidates'],
                 stats['fitting_primary_splits']])
table('natural_table.tex', 'Complete raw-scan paired median time ratios. Values above one favor the primary policy; its kernel was dormant in every case.',
      'tab:natural', 'lrrrrr', ['Diagram', '$n$', 'Fitting/primary', 'Fitting/control', 'Primary calls', 'Primary splits'], rows)

rows = []
for x in ALG['fields']:
    def trial(arm):
        result = x['search']['results'][arm]
        return str(result['metrics']['candidates']) + (' / yes' if result['found'] else ' / no')
    comp = x['compression']['results']
    var = str(x['scalar_variables']) + (r'$^\ast$' if not x['within_default_caps'] else '')
    rows.append([x['degree'], x['mixing'], var, trial('fitting'), trial('primary'),
                 f"{x['search']['timing']['median_fitting_over']['primary']:.3f}",
                 f"{x['compression']['timing']['median_fitting_over']['primary']:.3f}",
                 str(comp['fitting']['entries']) + r'$\to$' + str(comp['primary']['entries'])])
table('algebra_table.tex', 'Bounded algebraic search and complete recursive compression. Trial columns give candidates examined and whether a split was found. Both ratio columns are paired Fitting/primary medians. The starred case raises the variable cap.',
      'tab:algebra', 'rlrccrrc', ['$r$', 'Mixing', 'Variables', r'\shortstack{Old pass\\trials/split}', r'\shortstack{Primary pass\\trials/split}', r'\shortstack{Search\\ratio}', r'\shortstack{Full\\ratio}', r'\shortstack{Final entries\\old $\to$ primary}'], rows)

rows = [[x['degree'], x['fitting_success_numerator'], x['primary_success_numerator'], x['denominator']]
        for x in ALG['probabilities']['rows']]
table('probability_table.tex', 'Exact successful-pair counts for the uniform two-field comparison.',
      'tab:probability', 'rrrr', ['$r$', 'Fitting successes', 'Primary successes', 'All ordered pairs'], rows)

geonames = {'klein_even_256': 'Two Klein bottles', 'klein_even_4096': 'Two Klein bottles',
            'klein_even_65536': 'Two Klein bottles', 'torus_65536': 'One torus',
            'projective_cap_16384': 'Projective-plane/sphere cap',
            'genus_two_16384': 'Genus-two base', 'chain8_4096': 'Eight-patch closed chain'}
rows = [[geonames[x['name']], f"{x['input']['sheets']:,}",
         f"{1000*x['medians_seconds']['compressed']:.3f}",
         f"{1000*x['medians_seconds']['expanded']:.3f}"] for x in GEO['expansion']]
table('geometry_table.tex', 'Complete geometric preparation versus an independent literal-sheet oracle. Times are median milliseconds per query; this is not a comparison with another compressed algorithm.',
      'tab:geometry', 'lrrr', ['Assembly', 'Sheets', 'Compressed (ms)', 'Expanded (ms)'], rows)

log = (ROOT / 'validation/full_suite.log').read_text()
m = re.search(r'Ran (\d+) tests in ([\d.]+)s', log)
s = re.search(r'OK \(skipped=(\d+)\)', log)
if not m or not s:
    raise SystemExit('No completed successful full suite is available for the validation paragraph.')
(OUT / 'validation.tex').write_text(
    f"The complete final repository suite ran {m[1]} test methods in {m[2]} seconds: "
    f"{int(m[1])-int(s[1])} passed and {s[1]} were skipped because they require the optional native Regina dependency. "
    "The pinned baseline had 697 methods and one error in the partial-input worker regression; "
    "that error is repaired. The final suite adds 32 methods: twelve primary, five integration, "
    "fourteen geometric, and one malformed-byte worker regression. The retained full log records "
    "all method names and the independent enumeration totals.\n")

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.ticker import ScalarFormatter
plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 9, 'axes.titlesize': 11,
                     'axes.labelsize': 9, 'pdf.fonttype': 42, 'ps.fonttype': 42})
fig, axes = plt.subplots(1, 2, figsize=(10.6, 3.8), constrained_layout=True)
subset = [x for x in GEO['expansion'] if x['name'].startswith('klein_even_')]
xs = [x['input']['sheets'] for x in subset]
for key, label, color, marker in [('expanded', 'Literal expansion', '#b45f38', 's'),
                                  ('compressed', 'Compressed preparation', '#126c73', 'o')]:
    ys = [1000*x['medians_seconds'][key] for x in subset]
    axes[0].plot(xs, ys, color=color, marker=marker, linewidth=1.7, label=label)
axes[0].set(xscale='log', yscale='log', xlabel='Sheets W', ylabel='Median time (ms)',
            title='A. Avoiding sheet expansion')
axes[0].set_xticks(xs, [f'{x:,}' for x in xs])
axes[0].legend(frameon=False, loc='upper left', fontsize=8)
for pieces, color, marker in [(1, '#126c73', 'o'), (8, '#406aab', 's'), (64, '#b45f38', '^')]:
    rows = [x for x in GEO['binary'] if x['pieces'] == pieces]
    axes[1].plot([x['sheet_exponent'] for x in rows],
                 [1000*x['medians_seconds']['prepare'] for x in rows],
                 color=color, marker=marker, linewidth=1.7, label=f'{pieces} piece' + ('s' if pieces != 1 else ''))
axes[1].set(xscale='log', yscale='log', xlabel=r'Binary exponent $b$ in $W=2^b$',
            ylabel='Median preparation (ms)', title='B. Binary size and patch count')
axes[1].set_xticks([64, 1024, 4096, 16384], ['64', '1,024', '4,096', '16,384'])
axes[1].legend(frameon=False, loc='center left', fontsize=8)
for ax in axes:
    ax.grid(True, which='major', color='#dce2e6', linewidth=.65)
    ax.set_axisbelow(True)
    ax.spines[['top', 'right']].set_visible(False)
fig.savefig(OUT / 'geometry_scaling.pdf')
fig.savefig(OUT / 'geometry_scaling.png', dpi=180)
plt.close(fig)
print('Generated four tables, validation paragraph, and geometry figure from retained evidence.')
