"""Regenerate the article's measured geometric comparison figure."""
import json
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt


def main():
    root = Path(__file__).resolve().parents[1]
    batch = json.loads((root/'evidence/geometry/paired_batch_benchmark.json').read_text())
    census = json.loads((root/'evidence/validation/peeled_census_benchmark.json').read_text())
    plt.rcParams.update({'font.family':'DejaVu Sans', 'font.size':10,
                         'axes.spines.top':False, 'axes.spines.right':False,
                         'pdf.fonttype':42, 'savefig.facecolor':'white'})
    fig, axes = plt.subplots(1, 2, figsize=(10.5, 4.0), layout='constrained')
    colours = {'layered':'#15395b', 'unknot':'#087f8c',
               'trefoil':'#bc6429', 'figure_eight':'#845794'}
    labels = {'layered':'Layered torus', 'unknot':'Source unknot',
              'trefoil':'Source trefoil', 'figure_eight':'Source figure-eight'}
    for family in colours:
        rows = [r for r in batch['cases'] if r['family']==family]
        axes[0].plot([r['moves'] for r in rows],
                     [r['summary']['producer']['speedup'] for r in rows],
                     marker='o', markersize=4, linewidth=1.6,
                     color=colours[family], label=labels[family])
    for family in ('layered','unknot'):
        rows = [r for r in census['cases'] if r['family']==family]
        axes[1].plot([r['candidates'] for r in rows], [r['speedup'] for r in rows],
                     marker='o', markersize=4, linewidth=1.6,
                     color=colours[family], label=labels[family])
    axes[0].set(title='One certified batch', xlabel='Same selected moves',
                ylabel='Sequential / simultaneous time')
    axes[1].set(title='Complete peeled-score census', xlabel='Current legal candidates',
                ylabel='Full replay / cold index time')
    for ax in axes:
        ax.set_xscale('log', base=2)
        ax.set_yscale('log')
        ax.set_xticks([1,4,8,16,32,64], labels=['1','4','8','16','32','64'])
        ax.grid(axis='y', which='major', color='#dce1e5', linewidth=.7)
        ax.legend(frameon=False, loc='upper left', fontsize=8)
    output = root/'article/figures'
    output.mkdir(parents=True, exist_ok=True)
    fig.savefig(output/'geometric_performance.pdf')
    fig.savefig(output/'geometric_performance.png', dpi=180)


if __name__ == '__main__':
    main()
