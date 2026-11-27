#!/usr/bin/env python3
"""Generate the static research figure from exact-form constants.csv.

This illustration is not used as a proof. Run verify_results.py first.
"""
from pathlib import Path
import csv
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.colors import Normalize

root = Path(__file__).resolve().parents[1]
with (root / 'data/constants.csv').open() as stream:
    rows = {int(r['N']): r for r in csv.DictReader(stream)}
plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 9,
                     'axes.titlesize': 11, 'axes.labelsize': 10,
                     'savefig.dpi': 200, 'pdf.fonttype': 42})
x = np.linspace(-0.66, -0.16, 800)
y = np.linspace(0.40, 0.91, 820)
X, Y = np.meshgrid(x, y)
Z = X + 1j * Y
fig, axes = plt.subplots(1, 2, figsize=(7.2, 3.95), sharex=True, sharey=True)
fig.subplots_adjust(left=.09, right=.87, bottom=.16, top=.84, wspace=.16)
normalization = Normalize(0, .16)
for ax, n in zip(axes, (3, 4)):
    row = rows[n]
    c = float(row['sharp_constant'])
    r = float(row['radial_minimizer'])
    theta = float(row['theta_radians'])
    values = np.maximum.reduce([np.abs(1 + Z**(2**j)) for j in range(n)])
    excess = values - c
    im = ax.pcolormesh(X, Y, excess, shading='auto', cmap='Blues', norm=normalization,
                      rasterized=True)
    levels = [.001, .01, .03, .06, .12]
    contours = ax.contour(X, Y, excess, levels=levels, colors='#34556a',
                          linewidths=.7, alpha=.8)
    ax.clabel(contours, levels=[.01, .06, .12], inline=True, fmt='%g', fontsize=7)
    ax.plot(x, -np.sqrt(3)*x, '--', color='#ad7750', lw=1.1, label='120-degree ray')
    ax.scatter([r*np.cos(theta)], [r*np.sin(theta)], s=46, c='#c84234',
               edgecolors='white', linewidths=1, zorder=10)
    ax.set_title(f'{n} filters: powers ' + (r'$1,2,4$' if n==3 else r'$1,2,4,8$') +
                 '\n' + rf'$c_{n}={c:.9f}$', loc='left', pad=10)
    ax.set_xlabel(r'$\operatorname{Re} z$')
    ax.set_xlim(x[0], x[-1]); ax.set_ylim(y[0], y[-1]); ax.set_aspect('equal')
    for spine in ax.spines.values(): spine.set_color('#7a8b96')
axes[0].set_ylabel(r'$\operatorname{Im} z$')
cbax = fig.add_axes([.90, .22, .022, .53])
colorbar = fig.colorbar(im, cax=cbax)
colorbar.set_label(r'Excess $\mathcal{M}_n(z)-c_n$', labelpad=6)
fig.text(.09, .05, 'Red points: proved minimizers. Dashed line: angle 120 degrees. Lower points follow by conjugation.',
         fontsize=8, color='#41505b')
(root / 'figures').mkdir(exist_ok=True)
fig.savefig(root / 'figures/extremal_geometry.pdf')
fig.savefig(root / 'figures/extremal_geometry.png')
plt.close(fig)
print('Created figures/extremal_geometry.pdf and .png')
