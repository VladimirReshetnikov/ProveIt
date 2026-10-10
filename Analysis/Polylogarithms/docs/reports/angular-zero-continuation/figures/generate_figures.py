"""Publication figures from the saved floating-point diagnostic data.

This file renders existing data. It does not establish any theorem and
does not regenerate, alter, or accept proof certificates.
"""
import json
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parent.parent
if (ROOT / 'data/diagnostics.json').exists():
    DATA = ROOT / 'data/diagnostics.json'
    OUT = ROOT / 'figures'
else:
    DATA = ROOT / 'agents/analytic/diagnostics.json'
    OUT = ROOT.parent / 'output/polylogarithms_continuation/figures'
OUT.mkdir(parents=True, exist_ok=True)
data = json.loads(DATA.read_text())
rows = data['angular_roots']
plt.rcParams.update({
    'font.family': 'serif', 'font.size': 10, 'axes.labelsize': 11,
    'axes.titlesize': 11, 'legend.fontsize': 9,
    'axes.spines.top': False, 'axes.spines.right': False,
    'pdf.fonttype': 42, 'ps.fonttype': 42,
    'axes.grid': True, 'grid.alpha': .18, 'grid.linewidth': .7,
})
palette = ['#244c78', '#bd562b', '#258070', '#835a91']

fig, ax = plt.subplots(1, 2, figsize=(9, 3.7), constrained_layout=True)
for a, col in zip([1, 2, 3, 5], palette):
    r = sorted((x for x in rows if x['a'] == a and x['b'] == 1),
               key=lambda x: x['radius'])
    ax[0].plot([x['radius'] for x in r], [x['theta'] for x in r],
               'o-', color=col, ms=3.5, lw=1.5, label=rf'$a={a}$')
for b, col in zip([.02, .3, 1, 4], palette):
    r = sorted((x for x in rows if x['a'] == 2 and x['b'] == b),
               key=lambda x: x['radius'])
    ax[1].plot([x['radius'] for x in r], [x['theta'] for x in r],
               'o-', color=col, ms=3.5, lw=1.5, label=rf'$b={b:g}$')
radius = np.linspace(0, 1, 201)
ax[1].plot(radius, np.arccos(radius/2), '--', color='.4', lw=1.2,
           label=r'$\arccos(\rho/2)$')
for p in ax:
    p.set(xlim=(0, 1.01), ylim=(1.015, 1.585), xlabel=r'Radius $\rho$')
    p.set_yticks([np.pi/3, 1.2, 1.4, np.pi/2],
                [r'$\pi/3$', '1.2', '1.4', r'$\pi/2$'])
    p.legend(loc='lower left', frameon=True, framealpha=.96)
ax[0].set_ylabel(r'Unique zero angle $\theta$ (radians)')
ax[0].set_title(r'(a) Outer order, at $b=1$', loc='left')
ax[1].set_title(r'(b) Harmonic exponent, at $a=2$', loc='left')
fig.savefig(OUT/'angular_geometry.pdf', metadata={'Title':'Angular-zero geometry'})
fig.savefig(OUT/'angular_geometry.png', dpi=200)
plt.close(fig)

fig, ax = plt.subplots(1, 2, figsize=(9, 3.35), constrained_layout=True)
for a, panel in [(1, ax[0]), (2, ax[1])]:
    for b, col in zip([.02, .3, 1, 4], palette):
        r = sorted((x for x in rows if x['a'] == a and x['b'] == b),
                   key=lambda x: x['radius'])
        xs = [0] + [x['radius'] for x in r]
        ys = [(1+2**(-b))*(2/3)**a/2] + [x['cos_theta']/x['radius'] for x in r]
        panel.plot(xs, ys, 'o-', color=col, ms=3.5, lw=1.5, label=rf'$b={b:g}$')
    panel.set(xlim=(0, 1.01), xlabel=r'Radius $\rho$')
    panel.set_title(rf'Outer order $a={a}$', loc='left')
    panel.legend(loc='center right', frameon=True, framealpha=.96)
ax[0].set_ylabel(r'Normalized displacement $\cos\theta/\rho$')
fig.savefig(OUT/'normalized_radius_conjecture.pdf',
            metadata={'Title':'Normalized-radius conjecture: numerical evidence'})
fig.savefig(OUT/'normalized_radius_conjecture.png', dpi=200)
plt.close(fig)

curves = {}
for r in rows:
    curves.setdefault((r['a'], r['b']), []).append(r)
strict = []
flat = []
for (a,b), r in curves.items():
    r.sort(key=lambda x:x['radius'])
    eta = [x['cos_theta']/x['radius'] for x in r]
    if (a,b)==(1,1):
        flat.extend(abs(v-.5) for v in eta)
    else:
        direction = 1 if a==1 and b<1 else -1
        strict.extend(direction*(eta[j+1]-eta[j]) for j in range(len(eta)-1))
assert min(strict)>0
report = {'status':'floating-point evidence for an explicitly unproved conjecture',
          'curves':len(curves),'strict_adjacent_comparisons':len(strict),
          'minimum_signed_gap':min(strict),'maximum_exact_case_error':max(flat),
          'source_root_count':len(rows)}
print(json.dumps(report, indent=2))
target = OUT.parent/'data/normalized_radius_diagnostics.json'
target.parent.mkdir(parents=True, exist_ok=True)
target.write_text(json.dumps(report,indent=2)+'\n')
