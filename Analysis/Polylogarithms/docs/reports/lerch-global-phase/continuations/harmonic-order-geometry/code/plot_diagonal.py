#!/usr/bin/env python3
"""Plot the existing A=2 diagonal-coefficient diagnostics.

No coefficients or critical parameters are recomputed. The JSON contains
exact coefficient intervals and separate high-precision numerical model
values. This figure uses the latter after conversion to ordinary plotting
precision. The inverse-sheet accessibility and dominance remain conjectural.

Example:
    python3 code/plot_diagonal.py --data data/diagonal_quantitative.json \
        --output-dir figures
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data', type=Path,
                        default=Path(__file__).resolve().parents[1]/'data'/'diagonal_quantitative.json')
    parser.add_argument('--output-dir', type=Path,
                        default=Path(__file__).resolve().parents[1]/'figures')
    args = parser.parse_args()
    report = json.loads(args.data.read_text(encoding='utf-8'))
    values = report['coefficient_data']
    assert [row['n'] for row in values] == list(range(50, 201))
    args.output_dir.mkdir(parents=True, exist_ok=True)

    import numpy as np
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.ticker import MultipleLocator, FormatStrFormatter

    plt.rcParams.update({
        'font.family': 'serif',
        'font.serif': ['DejaVu Serif'],
        'mathtext.fontset': 'dejavuserif',
        'font.size': 9.4,
        'axes.labelsize': 10.0,
        'axes.titlesize': 10.2,
        'xtick.labelsize': 8.8,
        'ytick.labelsize': 8.8,
        'axes.linewidth': 0.7,
        'pdf.fonttype': 42,
        'ps.fonttype': 42,
        'savefig.facecolor': 'white',
    })
    navy, teal, orange = '#243D57', '#287F7A', '#C67A35'
    grid = '#DEE3E8'
    fig, axes = plt.subplots(1, 2, figsize=(8.2, 3.7))
    parameters = report['parameters']
    chi = complex(float(parameters['square_root_coefficient']['real']),
                  float(parameters['square_root_coefficient']['imag']))
    theta = float(parameters['theta'])
    n_values = np.array([row['n'] for row in values], dtype=float)
    normalized = np.array([float(row['normalized_velocity']) for row in values])

    left = axes[0]
    visible = n_values <= 90
    smooth_n = np.linspace(50, 90, 2401)
    leading = np.real(chi*np.exp(-1j*smooth_n*theta))
    left.plot(smooth_n, leading, color=teal, lw=1.1,
              label=r'$\Re(\chi e^{-in\theta})$', zorder=2)
    left.plot(n_values[visible], normalized[visible], linestyle='none',
              marker='o', markersize=3.5, markeredgewidth=0.9,
              markeredgecolor=navy, markerfacecolor='white',
              label=r'Coefficient values $Z_n$', zorder=3)
    left.axhline(0, color='#A6AFB9', lw=0.65, zorder=1)
    left.set_xlim(49.5, 90.5)
    left.set_ylim(-1.78, 1.78)
    left.xaxis.set_major_locator(MultipleLocator(10))
    left.xaxis.set_minor_locator(MultipleLocator(5))
    left.yaxis.set_major_locator(MultipleLocator(0.5))
    left.set_xlabel(r'Index $n$')
    left.set_ylabel(r'Normalized velocity $Z_n$')
    left.set_title('(a) Coefficients and candidate phase', loc='left', pad=11)
    left.legend(loc='upper center', bbox_to_anchor=(0.5, -0.225),
                frameon=False, ncol=1, fontsize=8.4, handlelength=2.4,
                borderaxespad=0, labelspacing=0.45)

    right = axes[1]
    leading_scaled = np.array([float(row['n_times_leading_error']) for row in values])
    corrected_scaled = np.array([float(row['n_squared_times_corrected_error'])
                                 for row in values])
    right.plot(n_values, leading_scaled, color=teal, lw=0.9, alpha=0.92,
               label=r'$n\,|Z_n-Z_n^{(0)}|$', zorder=2)
    right.plot(n_values, corrected_scaled, color=orange, lw=0.9, alpha=0.86,
               linestyle=(0, (3.0, 1.5)),
               label=r'$n^2\,|Z_n-Z_n^{(1)}|$', zorder=3)
    right.set_xlim(48, 202)
    right.set_ylim(0, 0.535)
    right.xaxis.set_major_locator(MultipleLocator(50))
    right.xaxis.set_minor_locator(MultipleLocator(25))
    right.yaxis.set_major_locator(MultipleLocator(0.1))
    right.yaxis.set_major_formatter(FormatStrFormatter('%.1f'))
    right.set_xlabel(r'Index $n$')
    right.set_ylabel('Scaled absolute error')
    right.set_title('(b) Residuals after rescaling', loc='left', pad=11)
    right.legend(loc='upper center', bbox_to_anchor=(0.5, -0.225),
                 frameon=False, ncol=1, fontsize=8.4, handlelength=2.4,
                 borderaxespad=0, labelspacing=0.45)

    for ax in axes:
        ax.grid(axis='y', color=grid, linewidth=0.65)
        ax.set_axisbelow(True)
        ax.spines['top'].set_visible(False)
        ax.spines['right'].set_visible(False)
        ax.tick_params(which='major', length=3.5, width=0.7)
        ax.tick_params(which='minor', length=2, width=0.5, color='#8A939D')

    fig.subplots_adjust(left=0.085, right=0.988, bottom=0.265,
                        top=0.89, wspace=0.33)
    for extension, options in [('pdf', {}), ('png', {'dpi': 300})]:
        target = args.output_dir/f'diagonal_velocity_asymptotics.{extension}'
        fig.savefig(target, bbox_inches='tight', pad_inches=0.055, **options)
        print(target)
    plt.close(fig)


if __name__ == '__main__':
    main()
