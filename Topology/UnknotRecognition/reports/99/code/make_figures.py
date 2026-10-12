"""Regenerate article figures from the preserved raw benchmark results."""
from pathlib import Path
import csv
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.ticker import ScalarFormatter

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / 'article' / 'figures'
DEST.mkdir(parents=True, exist_ok=True)

def read_csv(path):
    with path.open(newline='', encoding='utf-8') as stream:
        return list(csv.DictReader(stream))

native = read_csv(ROOT / 'results/native/mobius_benchmark.csv')
finite = read_csv(ROOT / 'results/forest_search/benchmark.csv')
plt.rcParams.update({'font.size': 9, 'axes.titlesize': 10,
                     'axes.labelsize': 9, 'pdf.fonttype': 42,
                     'svg.fonttype': 'none'})
fig, axes = plt.subplots(1, 2, figsize=(9, 3.65), constrained_layout=True)
navy, teal, orange = '#18354A', '#007B83', '#BA5E27'
ax = axes[0]
x = [int(row['copies']) for row in native]
ax.plot(x, [float(row['native_total_ms']) for row in native],
        color=teal, marker='o', label='Native + independent replay')
ax.plot(x, [float(row['regina_total_ms']) for row in native],
        color=navy, marker='s', label='Regina complete cut query')
ax.set_xscale('log', base=4)
ax.set_xticks(x)
ax.xaxis.set_major_formatter(ScalarFormatter())
ax.set_xlabel('Parallel-surface copies')
ax.set_title('A. Supplied normal cuts')
ax = axes[1]
x = [int(row['rank']) for row in finite]
for key, color, marker, label in [
    ('enum_ms', navy, 's', 'Specified tree enumeration'),
    ('degree2_ms', teal, 'o', 'Polynomial selection'),
    ('search_ms', orange, '^', 'Stopping-set search')]:
    ax.plot(x, [float(row[key]) for row in finite], color=color,
            marker=marker, label=label)
ax.set_xticks(x)
ax.set_xlabel('Dual graph rank k (2k rows)')
ax.set_title('B. Finite forest-selection queries')
for ax in axes:
    ax.set_yscale('log')
    ax.set_ylabel('Median complete query time (ms)')
    ax.grid(axis='y', alpha=.22, which='major')
    ax.spines[['top', 'right']].set_visible(False)
    ax.legend(loc='best', fontsize=7.2, frameon=False)
for extension in ('pdf', 'svg', 'png'):
    fig.savefig(DEST / f'benchmarks.{extension}', dpi=200,
                metadata={'Creator': 'ProveIt research; make_figures.py'}
                if extension == 'pdf' else None)
print('Wrote article/figures/benchmarks.{pdf,svg,png}')
