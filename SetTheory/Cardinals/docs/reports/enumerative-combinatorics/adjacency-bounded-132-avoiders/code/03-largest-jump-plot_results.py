"""Optional figures. Needs matplotlib; reads retained CSV data."""
from pathlib import Path
import csv
import math
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
root = Path(__file__).resolve().parents[1]
rows = list(csv.DictReader((root/'data'/'limit_probabilities.csv').open()))
x = [int(r['k']) for r in rows]
y = [float(r['tail_gt_k_decimal']) for r in rows]
fig, ax = plt.subplots(figsize=(7.0, 4.1))
ax.plot(x, [math.sqrt(math.pi*k)*t for k,t in zip(x,y)], label=r'$\sqrt{\pi k}\,\Pr(D>k)$')
ax.axhline(3, linestyle='--', label='Asymptotic constant 3')
ax.set_xlabel('Deficit threshold k')
ax.set_ylabel('Rescaled survival probability')
ax.legend(loc='lower right')
ax.grid(alpha=0.25)
fig.tight_layout()
fig.savefig(root/'figures'/'tail_scaling.pdf')
fig.savefig(root/'figures'/'tail_scaling.png', dpi=180)
plt.close(fig)
rows = list(csv.DictReader((root/'data'/'finite_histograms.csv').open()))
fig, ax = plt.subplots(figsize=(7.0, 4.1))
for n in (6, 9, 12):
    selected = [r for r in rows if int(r['n']) == n]
    ax.plot([int(r['deficit']) for r in selected],
            [float(r['probability']) for r in selected], marker='o', label=f'n = {n}')
limrows = list(csv.DictReader((root/'data'/'limit_probabilities.csv').open()))[:11]
ax.plot([int(r['k']) for r in limrows], [float(r['probability_decimal']) for r in limrows],
        linestyle='--', marker='s', label='Limiting law')
ax.set_xlabel('Deficit k')
ax.set_ylabel('Probability of deficit k')
ax.legend()
ax.grid(alpha=0.25)
fig.tight_layout()
fig.savefig(root/'figures'/'finite_probabilities.pdf')
fig.savefig(root/'figures'/'finite_probabilities.png', dpi=180)
plt.close(fig)
print('Wrote two separate figures from the retained exact data.')
