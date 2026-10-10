#!/usr/bin/env python3
"""Reproduce the two-panel Gaussian order-zero research figure.

Requires numpy, scipy, matplotlib, and data/gaussian_order_verification.json from
    python3 code/verify_gaussian_order.py --numeric --full --dps 45

The graph and floating-point roots are numerical diagnostics. The analytic
proof, not numerical plotting, establishes the complete real-zero theorem.
"""
from __future__ import annotations

import argparse
from functools import lru_cache
import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.ticker import FixedLocator, ScalarFormatter
import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq
from scipy.special import digamma, gammaln

C = np.pi / 2
NAVY, TEAL, ORANGE = '#17364d', '#198a8a', '#d18335'


@lru_cache(maxsize=4096)
def ratio(q: float) -> float:
    """R(q) from gamma-normalized integrals, using only real quadrature.

    The variable is v=(pi/2)*x. The gamma density keeps the peak near q
    at bounded scale and the partition prevents adaptive quadrature from
    missing it when q is large.
    """
    lognorm = gammaln(q + 1)
    spread = 10 * np.sqrt(q + 1)
    intervals = sorted(set([0., 1., q / 2, max(1., q - spread),
                            q, q + spread, 2 * q + 20])) + [np.inf]

    def density(v):
        return np.exp(q * np.log(v) - v - lognorm) if v > 0 else 0.

    def numerator(v):
        ell = np.euler_gamma + digamma(.5 + 1j * v / np.pi).real
        return density(v) * ell / (1 + np.exp(-2 * v))

    def denominator(v):
        e = np.exp(-2 * v)
        return density(v) * (1 - e) / (1 + e) ** 2

    def integrate(function):
        return sum(quad(function, a, b, epsabs=2e-12, epsrel=2e-12,
                        limit=120)[0]
                   for a, b in zip(intervals[:-1], intervals[1:]))

    return integrate(numerator) / (C * integrate(denominator))


def normalized_factor(q):
    return ratio(float(q)) * np.cos(C * q) - np.sin(C * q)


def approximations(m):
    n = 2 * np.asarray(m) + 1
    lam = np.log(n / np.pi) + np.euler_gamma
    e0 = np.arctan(C / lam) / C
    e1 = e0 - (.5 - e0) / (n * (lam ** 2 + C ** 2))
    return e0, e1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path,
                        default=Path(__file__).resolve().parents[1]/'data'/'gaussian_order_verification.json')
    parser.add_argument('--prefix', type=Path,
                        default=Path(__file__).resolve().parents[1]/'figures'/'harmonic_order_zeros')
    parser.add_argument('--data-output', type=Path,
                        default=Path(__file__).resolve().parents[1]/'data'/'harmonic_order_zeros_plot_data.json')
    args = parser.parse_args()
    args.prefix.parent.mkdir(parents=True, exist_ok=True)
    args.data_output.parent.mkdir(parents=True, exist_ok=True)
    report = json.loads(args.input.read_text())
    wanted = [1, 2, 3, 5, 10, 50, 500]
    root_records = {row['m']: row for row in report['numeric']['roots']}
    missing = set(wanted) - root_records.keys()
    if missing:
        raise RuntimeError(f'Missing m={sorted(missing)}; run full diagnostics first.')
    m_sample = np.array(wanted)
    epsilon = np.array([float(root_records[m]['epsilon']) for m in wanted])

    q_grid = np.linspace(2., 12., 501)
    factor_grid = np.array([normalized_factor(q) for q in q_grid])
    q_roots = [brentq(normalized_factor, 2 * m, 2 * m + 1,
                     xtol=4e-14, rtol=2e-14) for m in range(1, 6)]
    for m in [1, 2, 3, 5]:
        # A meaningful independent implementation comparison: SciPy quadrature
        # and brentq here versus the mpmath computations in data/gaussian_order_verification.json.
        assert abs(q_roots[m - 1] + float(root_records[m]['zero'])) < 3e-11
    m_curve = np.geomspace(1., 500., 501)
    e0, e1 = approximations(m_curve)

    plt.rcParams.update({
        'font.family': 'DejaVu Sans', 'font.size': 8.4,
        'mathtext.fontset': 'dejavusans', 'axes.titlesize': 9.,
        'axes.titleweight': 'semibold', 'axes.labelsize': 9.,
        'xtick.labelsize': 7.8, 'ytick.labelsize': 7.8,
        'legend.fontsize': 7.4, 'axes.spines.top': False,
        'axes.spines.right': False, 'axes.linewidth': .65,
        'xtick.major.width': .65, 'ytick.major.width': .65,
        'pdf.fonttype': 42, 'ps.fonttype': 42,
        'savefig.facecolor': 'white',
    })
    fig, (left, right) = plt.subplots(1, 2, figsize=(7.3, 3.8))
    fig.subplots_adjust(left=.082, right=.985, top=.79, bottom=.27, wspace=.32)

    for m in range(1, 6):
        left.axvspan(2 * m, 2 * m + 1, color=TEAL, alpha=.075, lw=0)
    left.axhline(0, color='#9ba7ae', linewidth=.7, zorder=1)
    left.plot(q_grid, factor_grid, color=NAVY, linewidth=1.5,
              label='Numerical factor')
    left.scatter(q_roots, np.zeros(5), s=22, facecolors='white',
                 edgecolors=TEAL, linewidths=1.2, zorder=4,
                 label='Approximate zeros')
    left.set(xlim=(2, 12), ylim=(-1.68, 1.68), xlabel='$q=-s$',
             ylabel='$F(q)$', title='a  Unique real zeros')
    left.set_xticks(np.arange(2, 13, 2))
    left.set_yticks([-1.5, 0, 1.5])
    left.grid(axis='y', color='#e5e9ec', linewidth=.5)
    left.legend(loc='upper center', bbox_to_anchor=(.5, -.27),
                frameon=False, ncol=2, borderaxespad=0., handlelength=1.6,
                columnspacing=1.)

    right.plot(m_curve, e0, color=TEAL, linewidth=1.3, linestyle='--',
               dashes=(4, 2), label='Arctangent approximation')
    right.plot(m_curve, e1, color=ORANGE, linewidth=1.3,
               label='First $1/N$ correction')
    right.scatter(m_sample, epsilon, color=NAVY, s=20, zorder=4,
                  label='Computed displacement')
    right.set(xscale='log', xlim=(.9, 560), ylim=(.10, .92),
              xlabel='Zero index $m$ (logarithmic scale)',
              ylabel=r'$\varepsilon_m=\sigma_m+2m+1$',
              title='b  Approach to the odd integers')
    right.xaxis.set_major_locator(FixedLocator([1, 5, 10, 50, 100, 500]))
    right.xaxis.set_major_formatter(ScalarFormatter())
    right.xaxis.set_minor_locator(FixedLocator([]))
    right.set_yticks([.2, .4, .6, .8])
    right.grid(axis='y', color='#e5e9ec', linewidth=.5)
    handles, labels = right.get_legend_handles_labels()
    order = [2, 0, 1]
    right.legend([handles[i] for i in order], [labels[i] for i in order],
                 loc='upper right', frameon=False, borderaxespad=.2,
                 handlelength=2.1)

    fig.text(.082, .952, 'Gaussian harmonic Dirichlet series',
             color=NAVY, size=11.3, weight='semibold')
    fig.text(.082, .892,
             r'$F(q)=R(q)\cos(\pi q/2)-\sin(\pi q/2)$', size=8.6)
    fig.text(.985, .892, 'Numerical illustrations of the analytic zero theorem',
             ha='right', size=6.9, color='#54656f')
    fig.text(.082, .036,
             'Shading: intervals containing exactly one zero. '
             'Decimals and curves are not certified interval enclosures.',
             size=7., color='#54656f')

    for extension in ('pdf', 'png'):
        output = args.prefix.with_suffix('.' + extension)
        fig.savefig(output, dpi=400, metadata={'Title': 'Gaussian order zeros'}
                    if extension == 'pdf' else None)
        print(f'Wrote {output}')
    plt.close(fig)

    data = {'classification': 'nonrigorous floating-point plot data',
            'scipy_quadrature_absolute_relative_tolerances': [2e-12, 2e-12],
            'q': q_grid.tolist(), 'normalized_factor': factor_grid.tolist(),
            'first_five_positive_q_zeros': q_roots,
            'm_samples': wanted, 'epsilon_samples': epsilon.tolist(),
            'm_approximation_grid': m_curve.tolist(),
            'arctangent_approximation': e0.tolist(),
            'first_index_correction': e1.tolist()}
    args.data_output.write_text(
        json.dumps(data, indent=2) + '\n')


if __name__ == '__main__':
    main()
