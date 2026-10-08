"""Regenerate exact operation-count figure; these curves are not timing fits."""
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.ticker import LogLocator, NullFormatter

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'figures'
OUT.mkdir(exist_ok=True)
plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 10,
                     'axes.labelcolor': '#17324D', 'text.color': '#17324D',
                     'axes.spines.top': False, 'axes.spines.right': False,
                     'pdf.fonttype': 42, 'ps.fonttype': 42})
sizes = [2 ** exponent - 1 for exponent in range(1, 11)]
forward = [size * (1 + 2 * size) for size in sizes]
reverse = [3 * size for size in sizes]
fig, ax = plt.subplots(figsize=(6.5, 3.45), layout='constrained')
ax.loglog(sizes, forward, color='#17324D', linewidth=2.2,
          label=r'Inherited forward: $M(1+2M)$')
ax.loglog(sizes, reverse, color='#167D9A', linewidth=2.2,
          label=r'Reverse: $3M$')
ax.scatter([255, 255], [130305, 765], s=30, color=['#17324D', '#167D9A'], zorder=4)
ax.vlines(255, 765, 130305, color='#8294A3', linestyle=':', linewidth=1.3)
ax.annotate('M = 255\n130,305 → 765 attempts', xy=(255, 10000),
            xytext=(0.56, 0.49), textcoords='axes fraction', fontsize=9,
            bbox={'boxstyle': 'round,pad=0.35', 'facecolor': 'white',
                  'edgecolor': '#D4DDE3'})
ax.set_xlabel(r'Number of sources and branches, $R=M$ (odd)')
ax.set_ylabel('Radical-edge propagation attempts')
ax.set_xlim(1, 1200)
ax.set_ylim(2, 4e6)
ax.grid(which='major', color='#E1E7EB', linewidth=0.6)
ax.legend(loc='upper left', frameon=False, fontsize=9.5)
ax.xaxis.set_minor_formatter(NullFormatter())
ax.yaxis.set_minor_formatter(NullFormatter())
for ext in ('pdf', 'png'):
    fig.savefig(OUT / f'directional_counts.{ext}', dpi=200,
                metadata={'Creator': 'Exact formulas from the shared-suffix theorem'})
plt.close(fig)
