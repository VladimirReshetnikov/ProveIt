#!/usr/bin/env python3
"""Regenerate article tables and the vector figure from recorded raw results."""
import argparse
import csv
import hashlib
import json
from pathlib import Path
from statistics import median

ROOT = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--fast-root', type=Path, default=ROOT.parent / 'reproducibility' /
    'ProveIt/Topology/UnknotRecognition/fast')
args = parser.parse_args()
bench_path = args.fast_root / 'results/modular_benchmarks.json'
audit_path = args.fast_root / 'results/modular_audit.json'
bench = json.loads(bench_path.read_text())
audit = json.loads(audit_path.read_text())
assert not bench['changed_sources']
assert all(row['complete'] for row in bench['rows'])
tables, figures = ROOT / 'tables', ROOT / 'figures'
tables.mkdir(exist_ok=True)
figures.mkdir(exist_ok=True)

def table(name, caption, label, columns, header, rows, footnote=''):
    content = [r'\begin{table}[htbp]', r'\centering\small',
               r'\caption{' + caption + '}', r'\label{' + label + '}',
               r'\begin{tabular}{@{}' + columns + '@{}}', r'\toprule',
               ' & '.join(header) + r'\\', r'\midrule']
    content += [' & '.join(map(str, row)) + r'\\' for row in rows]
    content += [r'\bottomrule', r'\end{tabular}']
    if footnote:
        content += [r'\par\smallskip\begin{minipage}{0.97\textwidth}\footnotesize',
                    footnote, r'\end{minipage}']
    content += [r'\end{table}', '']
    (tables / (name + '.tex')).write_text('\n'.join(content))

arithmetic = [r for r in bench['rows'] if r['scope'] == 'arithmetic-stream']
raw = [r for r in bench['rows'] if r['scope'] == 'raw-shadow']
disabled = {r['name']: r for r in bench['rows'] if r['scope'] == 'recognition-disabled-filters'}
labels = {'conway':'Conway', 'kinoshita_terasaka':'Kinoshita--Terasaka',
          'conway_sum_2':'Conway sum, 2 factors', 'conway_sum_8':'Conway sum, 8 factors',
          'hard_unknot_8':'Hard unknot 8', 'grid_scrambled_unknot':'Scrambled grid unknot',
          'stress_braid5_36':'Five-strand stress braid'}
dimension_rows, time_rows = [], []
for r in arithmetic:
    i = r['input']
    stats = r['samples'][0]['results']['modular_boundary'][0]['stats']
    dimension_rows.append([i['tail_repetitions'], i['suffix_crossings'], i['matching_count'],
        i['frontier'], stats['max_common_vertices'], stats['max_terminal_count'],
        stats['interior_vertices'], stats['modular_determinants']])
    times = r['median_seconds']
    time_rows.append([i['tail_repetitions'], f"{times['integer']:.6f}",
        f"{times['rational_boundary']:.6f}", f"{times['modular_boundary']:.6f}",
        f"{r['median_speedups']['modular_boundary']:.3f}",
        f"{r['modular_over_rational_speedup']:.3f}"])
table('dimensions', 'Actual repeated-query suffix dimensions.', 'tab:dimensions', 'rrrrrrrr',
      ['$k$', '$n$', 'Queries', '$b$', '$v$', '$t$', '$v-t$', 'Cofactors'], dimension_rows,
      'Here $k$ is the pure-tail repetition count, $n$ the suffix crossings, '
      '$b$ the frontier darts, $v$ the common black-fragment vertices, and $t=b/2$ '
      'the terminals. Cofactors counts distinct terminal partitions actually evaluated. '
      'The last row intentionally uses only the first 50 of 200 available matchings.')
table('arithmetic', 'Fresh-setup repeated-query times and paired speed ratios.', 'tab:arithmetic',
      'rrrrrr', ['$k$', 'Integer (s)', 'Rational (s)', 'Modular (s)', 'Int./mod.', 'Rat./mod.'],
      time_rows, 'Times are medians of five complete rounds. Ratios are medians of '
      'within-round ratios, so they need not equal ratios of the displayed medians. '
      'A ratio above one favors the modular evaluator. Prime $65521$ is used throughout.')
raw_rows = []
for r in raw:
    times = r['median_seconds']
    raw_rows.append([labels[r['name']], f"{1000*times['integer']:.3f}",
        f"{1000*times['modular']:.3f}", f"{r['median_speedups']['modular']:.3f}",
        f"{disabled[r['name']]['median_speedups']['modular']:.3f}"])
table('recognition', 'The raw scans do not show an overall recognition gain.', 'tab:recognition',
      'lrrrr', ['Input', 'Integer (ms)', 'Modular (ms)', 'Raw ratio', 'Filters off'], raw_rows,
      'The first two columns time raw shadow scans. Raw ratio is the paired '
      'integer/modular ratio in that scope. Filters off is the corresponding ratio '
      'through the public recognition pipeline with its earlier filters disabled. '
      'All seven ordinary default-filter runs stop before either shadow backend.')
t = audit['totals']
audit_items = [('Diagrams, including mirrors', 'diagrams'),
    ('Independent reduced $\\F_2$ cubes', 'full_reduced_cubes'),
    ('Cube generators and checked $d^2$ columns', 'cube_generators'),
    ('Proper prefixes', 'proper_prefixes'),
    ('Actual matching completions', 'actual_matching_completions'),
    ('Modular vector comparisons over six primes', 'modular_vector_comparisons'),
    ('Bounds compared with full reduced homology', 'bounds_checked_against_full_homology'),
    ('Certified adaptive threshold agreements', 'certified_threshold_agreements'),
    ('Final capped ranks and recognition statuses', 'recognition_status_comparisons'),
    ('Positive modular claims replayed', 'positive_modular_replays')]
table('audit', 'Reproducible audit against independent reduced cubes and integer completions.',
      'tab:audit', 'lr', ['Check', 'Count'], [[name, f'{t[key]:,}'] for name,key in audit_items])

with (tables / 'measurements.csv').open('w', newline='') as f:
    w = csv.writer(f)
    w.writerow(['scope','name','arm','median_seconds','median_integer_over_arm'])
    for row in bench['rows']:
        for arm,value in row['median_seconds'].items():
            w.writerow([row['scope'],row['name'],arm,value,row['median_speedups'].get(arm,'')])

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.ticker import ScalarFormatter
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':9,'axes.spines.top':False,
    'axes.spines.right':False,'axes.labelcolor':'#182f49','text.color':'#182f49',
    'axes.edgecolor':'#8b9aa8','pdf.fonttype':42,'ps.fonttype':42})
fig, axes = plt.subplots(2,1,figsize=(7.1,6.6),gridspec_kw={'height_ratios':[1,1.25]},
                         layout='constrained')
ax = axes[0]
for numerator,color,marker,offset,label in [
    ('integer','#193a5a','o',-.07,'Maintained integer / modular'),
    ('rational_boundary','#00838b','s',.07,'Earlier rational / modular')]:
    points=[]; lows=[]; highs=[]
    for r in arithmetic:
        ratios=[s['seconds'][numerator]/s['seconds']['modular_boundary'] for s in r['samples']]
        mid=median(ratios); points.append(mid); lows.append(mid-min(ratios)); highs.append(max(ratios)-mid)
    ax.errorbar([j+offset for j in range(len(points))],points,yerr=[lows,highs],
                fmt=marker,color=color,capsize=3,markersize=5,lw=1.2,label=label)
ax.axhline(1,color='#89929a',lw=1,ls='--')
ax.set_yscale('log'); ax.set_ylim(.35,45)
ax.set_yticks([.5,1,2,5,10,20,40]); ax.yaxis.set_major_formatter(ScalarFormatter())
ax.set_xticks(range(5),['0 / 200','3 / 200','15 / 200','47 / 200','127 / 50'])
ax.set_xlabel('Interior vertices / queried matchings')
ax.set_ylabel('Time ratio (log scale)')
ax.set_title('A. Repeated suffix observations, including fresh setup',loc='left',fontweight='bold',fontsize=10)
ax.grid(axis='y',alpha=.16); ax.legend(loc='upper left',fontsize=8,frameon=False)
ax = axes[1]
for j,r in enumerate(raw):
    ratios=[s['seconds']['integer']/s['seconds']['modular'] for s in r['samples']]
    m=median(ratios)
    ax.errorbar(m,j,xerr=[[m-min(ratios)],[max(ratios)-m]],fmt='o',color='#193a5a',capsize=3,ms=5)
    ax.text(.035,j,f'{m:.3f}',va='center',fontsize=8,color='#526273')
ax.set_yticks(range(7),[labels[r['name']].replace('--','–') for r in raw])
ax.invert_yaxis(); ax.set_xlim(0,1.3); ax.set_xticks([0,.25,.5,.75,1,1.25])
ax.axvline(1,color='#89929a',lw=1,ls='--'); ax.grid(axis='x',alpha=.16)
ax.set_xlabel('Maintained integer time / modular time')
ax.set_title('B. Complete raw shadow scans',loc='left',fontweight='bold',fontsize=10)
fig.savefig(figures/'performance.pdf',metadata={'Title':'Modular boundary response performance',
    'Subject':'Five paired rounds; intervals show observed min/max, not confidence intervals'})
fig.savefig(figures/'performance.png',dpi=180)
plt.close(fig)
manifest={'description':'Generated from recorded raw results, without rerunning timings.',
    'benchmarks_sha256':hashlib.sha256(bench_path.read_bytes()).hexdigest(),
    'audit_sha256':hashlib.sha256(audit_path.read_bytes()).hexdigest(),
    'rounds':bench['rounds'],'figure_intervals':'Minimum and maximum observed paired ratios; not confidence intervals.'}
(ROOT/'assets_provenance.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'tables':5,'figure':'figures/performance.pdf','rounds':bench['rounds']}))
