#!/usr/bin/env python3
"""Reproduce numerical illustrations; never used as a proof of RH or the theorem."""
import json
from pathlib import Path
import mpmath as mp
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from positive_filters import PositiveFilter, sinc

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'evidence'
FIG = ROOT / 'figures'
OUT.mkdir(exist_ok=True)
FIG.mkdir(exist_ok=True)
mp.mp.dps = 70
zeros = []
n = 1
while True:
    g = mp.im(mp.zetazero(n))
    if g > 200:
        break
    zeros.append(g)
    n += 1
(OUT/'zeta_ordinates_70digits.json').write_text(json.dumps({
    'status': 'mpmath approximations, not interval-certified',
    'positive_ordinates': [str(g) for g in zeros],
    'first_excluded_ordinate': str(g),
    'working_decimal_precision': mp.mp.dps,
}, indent=2)+'\n')

reports = []
filters = {}
for B in [50, 100, 200]:
    roots = [g for g in zeros if g <= B]
    filt = PositiveFilter(roots, B)
    filters[B] = filt
    root_residual = max(abs(filt.transform(g)) for g in roots)
    # All these inequalities are numerical smoke checks. Universal bounds are proved in TEX.
    for f in filt.factors:
        assert mp.fsum(abs(a) for a in f.coefficients) < mp.mpf(1)/11
        assert max(abs(f.transform(g)) for g in f.frequencies) < mp.mpf('1e-60')
    assert root_residual < mp.mpf('1e-60')
    frequencies = [mp.mpf(B)*(1+mp.mpf(k)/100) for k in range(401)]
    worst_ratio = max(abs(filt.transform(x))/filt.tail_bound for x in frequencies)
    assert worst_ratio <= 1 + mp.mpf('1e-60')
    reports.append({
        'cutoff': B,
        'number_positive_ordinates': len(roots),
        'colors': len(filt.colors),
        'color_sizes': [len(c) for c in filt.colors],
        'damping_count': filt.damping_count,
        'support_radius': str(filt.radius),
        'old_one_uniform_per_positive_ordinate_radius': str(mp.pi*mp.fsum(1/g for g in roots)),
        'jensen_lower_for_this_list': str(mp.pi/B*mp.fsum(mp.log(B/g) for g in roots)),
        'tail_bound': str(filt.tail_bound),
        'root_residual_max': str(root_residual),
        'sampled_tail_to_bound_ratio_max': str(worst_ratio),
        'factor_diagnostics': [f.diagnostics() for f in filt.factors],
    })
(OUT/'numerical_results.json').write_text(json.dumps({
    'status': 'illustrative high-precision computations; no interval-certified zeta zero list',
    'mpmath_version': mp.__version__,
    'reports': reports,
}, indent=2)+'\n')

plt.rcParams.update({'font.family':'DejaVu Sans', 'font.size':10,
                    'axes.spines.top':False, 'axes.spines.right':False})
filt = filters[100]
xx = np.linspace(0, 160, 1201)
low = np.array([float(abs(filt.low_transform(mp.mpf(x)))) for x in xx])
full = np.array([float(abs(filt.transform(mp.mpf(x)))) for x in xx])
fig, ax = plt.subplots(figsize=(9, 4.2))
ax.plot(xx, np.log10(np.maximum(low, 1e-100)), color='#6395a6', lw=1.1, label='Exact-zero factors (numerical evaluation)')
ax.plot(xx, np.log10(np.maximum(full, 1e-100)), color='#144f60', lw=1.6, label='With high-frequency damping')
ax.axvline(100, color='#888888', linestyle='--', lw=.8)
ax.axhline(float(mp.log10(filt.tail_bound)), color='#ad633b', linestyle='--', lw=1.2, label='Proved bound beyond B = 100')
ax.scatter([float(g) for g in zeros if g<=100], [-94]*len([g for g in zeros if g<=100]),
           marker='|', s=35, color='#ad633b', label='Prescribed positive ordinates')
ax.set(xlabel='Frequency', ylabel='log10 of multiplier magnitude', xlim=(0,160), ylim=(-100,1))
ax.legend(loc='upper right', fontsize=8, frameon=False)
fig.tight_layout()
fig.savefig(FIG/'filter_response.pdf')
fig.savefig(FIG/'filter_response.png', dpi=170)
plt.close(fig)

# A separate figure displays the positive density of one separated factor.
factor = filt.factors[0]
tt = np.linspace(-float(factor.radius), float(factor.radius), 801)
dd = [float(factor.density(mp.mpf(t))) for t in tt]
base = [max(0,1-abs(t)/float(factor.radius))/float(factor.radius) for t in tt]
fig, ax = plt.subplots(figsize=(9,3.1))
ax.fill_between(tt, np.array(base)*5/6, np.array(base)*6/5, color='#d9e9ee', label='Proved positive envelope')
ax.plot(tt, dd, color='#144f60', lw=1.3, label='Constructed factor density')
ax.set(xlabel='Logarithmic offset', ylabel='Density', xlim=(tt[0],tt[-1]), ylim=(0,None))
ax.legend(fontsize=9, frameon=False)
fig.tight_layout()
fig.savefig(FIG/'positive_factor.pdf')
fig.savefig(FIG/'positive_factor.png', dpi=170)
plt.close(fig)
print(json.dumps({'completed':True,'cutoffs':[50,100,200],
                  'positive_zeros':len(zeros),'root_residuals':[r['root_residual_max'] for r in reports]},indent=2))
