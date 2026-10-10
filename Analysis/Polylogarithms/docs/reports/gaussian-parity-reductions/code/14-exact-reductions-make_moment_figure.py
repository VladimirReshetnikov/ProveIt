#!/usr/bin/env python3
"""Reproduce the two-panel log-Gamma moment diagnostic figure.

Requirements: Python 3, mpmath, numpy, matplotlib.
Run: python make_moment_figure.py

The positive coefficients are computed from their defining coefficient
recurrence; the asymptotic formulas are used only as comparison curves.
No existing executable module from the research package is imported.
Numerical data are diagnostics, not interval certificates or proofs.
"""
from pathlib import Path
import json
import math
import mpmath as mp
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.ticker import ScalarFormatter, MultipleLocator

OUT = Path(__file__).resolve().parent
mp.mp.dps = 70
K_MAX = 240
TAU = mp.findroot(lambda t: -t * mp.digamma(1 - t) - 1,
                 (mp.mpf('0.45'), mp.mpf('0.55')))
RHO = TAU / mp.gamma(1 - TAU)
ALPHA = -mp.log(RHO)
V = 1 + TAU**2 * mp.polygamma(1, 1 - TAU)
C = TAU / mp.sqrt(2 * mp.pi * V)
KAPPA3 = (1 + 3 * TAU**2 * mp.polygamma(1, 1 - TAU)
          - TAU**3 * mp.polygamma(2, 1 - TAU))
KAPPA4 = (1 + 7 * TAU**2 * mp.polygamma(1, 1 - TAU)
          - 6 * TAU**3 * mp.polygamma(2, 1 - TAU)
          + TAU**4 * mp.polygamma(3, 1 - TAU))
BETA1 = (-1 / (2 * V) + KAPPA3 / (2 * V**2)
         + KAPPA4 / (8 * V**2) - 5 * KAPPA3**2 / (24 * V**3))

# d_j = j [u^j] log Gamma(1-u).  All d_j are positive.
d = [mp.mpf(0), mp.euler] + [mp.zeta(j) for j in range(2, K_MAX)]
coefficients = []
for k in range(1, K_MAX + 1):
    # If a_m=[u^m] Gamma(1-u)^k, logarithmic differentiation gives
    # m a_m = k sum_{j=1}^m d_j a_{m-j}, a_0=1; c_k=a_{k-1}/k.
    a = [mp.mpf(1)]
    for m in range(1, k):
        a.append(k * mp.fsum(d[j] * a[m-j]
                            for j in range(1, m+1)) / m)
    ck = a[k-1] / k
    assert ck > 0
    coefficients.append(ck)

ks = np.arange(1, K_MAX + 1)
leading_ratios = []
corrected_ratios = []
for k, ck in zip(ks, coefficients):
    leading = C * RHO**(-int(k)) * mp.mpf(int(k))**mp.mpf('-1.5')
    leading_ratios.append(ck / leading)
    corrected_ratios.append(ck / (leading * (1 + BETA1 / int(k))))

ns = (20, 40, 80)
log_terms = {
    n: [mp.log10(ck) - n * mp.log10(k)
        for k, ck in enumerate(coefficients, start=1)] for n in ns
}
minima = {}
for n in ns:
    i = min(range(K_MAX), key=lambda j: log_terms[n][j])
    minima[n] = {'k': i + 1, 'log10_magnitude': float(log_terms[n][i]),
                 'n_over_alpha': float(n / ALPHA)}

plt.rcParams.update({
    'font.family': 'DejaVu Serif',
    'font.size': 8.2,
    'mathtext.fontset': 'dejavuserif',
    'axes.titlesize': 9.2,
    'axes.labelsize': 8.2,
    'axes.linewidth': 0.7,
    'axes.edgecolor': '#68717b',
    'axes.labelcolor': '#1c2530',
    'xtick.color': '#374151',
    'ytick.color': '#374151',
    'xtick.labelsize': 7.6,
    'ytick.labelsize': 7.6,
    'legend.fontsize': 7.5,
    'legend.frameon': False,
    'pdf.fonttype': 42,
    'ps.fonttype': 42,
    'savefig.facecolor': 'white',
})
fig, axes = plt.subplots(1, 2, figsize=(7.3, 3.16),
                         gridspec_kw={'width_ratios': [1, 1.04]})
fig.subplots_adjust(left=0.095, right=0.985, bottom=0.22, top=0.88, wspace=0.32)
navy, teal = '#214f76', '#147d79'
colors = {20: navy, 40: '#7f4c99', 80: '#b35b3b'}

ax = axes[0]
mask = ks >= 8
err0 = np.array([float(abs(r-1)) for r in leading_ratios])
err1 = np.array([float(abs(r-1)) for r in corrected_ratios])
ax.loglog(ks[mask], err0[mask], color=navy, lw=1.7,
          label='Leading term')
ax.loglog(ks[mask], err1[mask], color=teal, lw=1.7,
          label='First correction')
ax.set_title('(a) Coefficient approximations', loc='left', pad=9)
ax.set_xlabel(r'Coefficient index $k$')
ax.set_ylabel('Absolute relative error')
ax.set_xlim(8, K_MAX)
ax.set_ylim(8e-7, 6e-2)
ax.set_xticks([10, 20, 50, 100, 200])
ax.xaxis.set_major_formatter(ScalarFormatter())
ax.grid(axis='y', which='major', color='#d9dfe5', lw=0.65)
ax.legend(loc='upper right', handlelength=2.2, labelspacing=0.75)
ax.text(0.03, 0.06, r'$L_k=C\rho^{-k}k^{-3/2}$', transform=ax.transAxes,
        fontsize=8.2, color='#374151')

ax = axes[1]
for n in ns:
    y = np.array([float(z) for z in log_terms[n]])
    ax.plot(ks, y, color=colors[n], lw=1.6, label=rf'$n={n}$')
    ax.axvline(float(n / ALPHA), color=colors[n], lw=0.8,
               linestyle=(0, (2, 3)), alpha=0.55, zorder=0)
    ax.plot(minima[n]['k'], minima[n]['log10_magnitude'], 'o',
            color=colors[n], ms=4.2, mec='white', mew=0.65, zorder=3)
ax.set_title('(b) Least terms and eventual growth', loc='left', pad=9)
ax.set_xlabel(r'Term index $k$')
ax.set_ylabel(r'$\log_{10}(c_k/k^n)$')
ax.set_xlim(0, K_MAX)
ax.set_ylim(-125, 95)
ax.set_xticks([0, 50, 100, 150, 200])
ax.yaxis.set_major_locator(MultipleLocator(50))
ax.grid(axis='y', color='#d9dfe5', lw=0.65)
ax.legend(loc='upper center', handlelength=2.0, ncol=1, labelspacing=0.45)
ax.text(0.98, 0.05, r'Dotted lines: $k=n/\alpha$', transform=ax.transAxes,
        ha='right', fontsize=7.1, color='#596471')

for ax in axes:
    ax.spines['top'].set_visible(False)
    ax.spines['right'].set_visible(False)
    ax.tick_params(which='both', direction='out', length=3)
    ax.tick_params(which='minor', length=1.8)

fig.text(0.095, 0.055,
         'Numerical diagnostics; all quantities are dimensionless.  '
         'Circles mark minima among the computed integer indices.',
         fontsize=6.7, color='#596471', ha='left')
metadata = {'Title': 'Late coefficients and divergent moment expansions',
            'Author': 'ProveIt research package',
            'Subject': 'Numerical diagnostics of proved log-Gamma moment asymptotics',
            'Keywords': 'log-gamma, Lagrange inversion, asymptotic expansion, moment'}
fig.savefig(OUT / 'moment_asymptotics.pdf', metadata=metadata)
fig.savefig(OUT / 'moment_asymptotics.png', dpi=320)
plt.close(fig)

caption = r'''Numerical diagnostics for the log-Gamma moment expansion.  (a) Absolute
relative errors of the leading approximation $L_k=C\rho^{-k}k^{-3/2}$ and the
first-corrected approximation $L_k(1+\beta_1/k)$, where $C$, $\rho$ and
$\beta_1$ have the exact definitions in the text.  The coefficient values
$c_k=k^{-1}[u^{k-1}]\Gamma(1-u)^k$ are computed by a positive recurrence at
70 decimal digits; they are not replaced by their asymptotic estimates.
(b) The actual logarithmic term magnitudes $\log_{10}(c_k/k^n)$ for
$n=20,40,80$, showing descent to a least term and subsequent growth.  Dotted
vertical lines mark $k=n/\alpha$, with $\alpha=-\log\rho$; circles mark the
smallest terms among the computed integer indices $1\le k\le240$.
The plotting data are numerical diagnostics.  Divergence for every fixed
$n$ and the error bound for a growing truncation order are established
analytically in the text.  Every plotted quantity is dimensionless.'''
(OUT / 'caption.tex').write_text(caption + '\n')

payload = {
    'status': 'Numerical diagnostics, not interval-certified values or proofs.',
    'source_commit': 'afed07429d3d37eceb6c8e9e54cf4da2d3f39d53',
    'precision_decimal_digits': mp.mp.dps,
    'coefficient_formula': 'c_k = (1/k) [u^(k-1)] Gamma(1-u)^k',
    'coefficient_recurrence': 'a_0=1; a_m=(k/m)*sum_{j=1}^m d_j*a_(m-j); d_1=EulerGamma, d_j=zeta(j); c_k=a_(k-1)/k',
    'units': 'All quantities are dimensionless; k and n are integer indices.',
    'constants': {name: mp.nstr(value, 60) for name, value in
                  [('tau', TAU), ('rho', RHO), ('alpha', ALPHA), ('v', V),
                   ('C', C), ('beta1', BETA1)]},
    'data': [{'k': int(k), 'c_k': mp.nstr(ck, 50),
              'ratio_to_leading': mp.nstr(r0, 40),
              'ratio_to_first_correction': mp.nstr(r1, 40),
              'log10_term': {str(n): mp.nstr(log_terms[n][int(k)-1], 40) for n in ns}}
             for k, ck, r0, r1 in zip(ks, coefficients, leading_ratios, corrected_ratios)],
    'sampled_minima': minima,
    'caption': caption,
}
(OUT / 'moment_asymptotics_data.json').write_text(json.dumps(payload, indent=2) + '\n')
print(json.dumps({'created': ['moment_asymptotics.pdf', 'moment_asymptotics.png',
                              'moment_asymptotics_data.json', 'caption.tex'],
                  'sampled_minima': minima}, indent=2))
