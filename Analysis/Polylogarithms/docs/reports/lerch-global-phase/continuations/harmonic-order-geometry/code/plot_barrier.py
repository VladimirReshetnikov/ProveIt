#!/usr/bin/env python3
"""Publication figure for the proved optimal exterior-barrier formulas.

The plotted numbers are diagnostic evaluations, not interval certificates.
Root solving uses 110 decimal digits. The small cutoff displacement is
computed as exp(alpha)*expm1(delta), avoiding subtraction of two huge
nearly equal values. Exact sample enclosures are supplied separately by
verify_optimal_barrier.py.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp


def evaluate(n: int) -> dict[str, mp.mpf]:
    phi = (1 + mp.sqrt(5)) / 2
    r = mp.findroot(lambda z: z**3 + n*z**2 - n*z - n, (1, phi))
    tau = (2-r)*mp.exp(-r)
    discr = mp.sqrt(n*n+8*n)
    alpha = (3*n-discr)/4
    A = alpha*(n-alpha)
    C = n-2*alpha
    E = mp.exp(alpha-n)
    delta = tau*A*E/discr
    for _ in range(30):
        poly = A+C*delta-delta**2
        exp_term = tau*E*mp.exp(delta)
        value = -discr*delta+2*delta**2+exp_term*poly
        derivative = -discr+4*delta+exp_term*(poly+C-2*delta)
        updated = delta-value/derivative
        if abs(updated-delta) < mp.mpf('1e-100')*max(abs(updated), mp.mpf('1e-50')):
            delta = updated
            break
        delta = updated
    else:
        raise ArithmeticError(f'Newton iteration did not converge at n={n}')
    assert delta > 0
    residual = (-discr*delta+2*delta**2
                +tau*E*mp.exp(delta)*(A+C*delta-delta**2))
    assert abs(residual) < mp.mpf('1e-95')
    displacement = mp.exp(alpha)*mp.expm1(delta)
    return {'n': mp.mpf(n), 'r': r, 'tau': tau, 'alpha': alpha,
            'delta': delta, 'displacement_per_n': displacement/n,
            'root_residual': residual}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output-dir', type=Path,
                        default=Path(__file__).resolve().parents[1]/'figures')
    parser.add_argument('--data-output', type=Path,
                        default=Path(__file__).resolve().parents[1]/'data'/'optimal_barrier_plot_data.json')
    args = parser.parse_args()
    args.data_output.parent.mkdir(parents=True, exist_ok=True)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    mp.mp.dps = 110
    values = [evaluate(n) for n in range(2, 101)]
    phi = (1+mp.sqrt(5))/2
    tau_limit = (2-phi)*mp.exp(-phi)
    cutoff_limit = tau_limit/(4*mp.e**2)
    first_correction = (7+3*mp.sqrt(5))/2
    second_correction = -(35+16*mp.sqrt(5))/10
    metadata = {
        'status': 'diagnostic high-precision evaluations of proved formulas',
        'decimal_precision': mp.mp.dps,
        'stable_cutoff_formula': 'exp(alpha_n)*expm1(eta_n-alpha_n)/n',
        'coefficient_asymptotic': 'tau_inf*(1+a1/n+a2/n^2)',
        'cutoff_asymptotic': 'tau_inf/(4*e^2)*(1+a1/n)',
        'asymptotic_curves_shown_from_n': 8,
        'tau_limit': mp.nstr(tau_limit, 80),
        'cutoff_limit': mp.nstr(cutoff_limit, 80),
        'a1': mp.nstr(first_correction, 80),
        'a2': mp.nstr(second_correction, 80),
        'data': [{k: int(v) if k == 'n' else mp.nstr(v, 80)
                  for k, v in row.items()} for row in values],
    }
    args.data_output.write_text(
        json.dumps(metadata, indent=2)+'\n', encoding='utf-8')

    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    import matplotlib.ticker as mticker
    from matplotlib.lines import Line2D

    plt.rcParams.update({
        'font.family': 'serif',
        'font.serif': ['DejaVu Serif'],
        'mathtext.fontset': 'dejavuserif',
        'font.size': 9.4,
        'axes.labelsize': 10.2,
        'axes.titlesize': 10.5,
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
    n_values = [int(row['n']) for row in values]
    mark_indices = [0, 1, 3, 8, 18, 48, 98]
    curves = [[float(row['tau']) for row in values],
              [float(row['displacement_per_n']) for row in values]]
    limits = [float(tau_limit), float(cutoff_limit)]
    asym_n = list(range(8, 101))
    asym_curves = [
        [float(tau_limit*(1+first_correction/n+second_correction/n**2)) for n in asym_n],
        [float(cutoff_limit*(1+first_correction/n)) for n in asym_n],
    ]
    titles = ['(a) Optimal operator coefficient', '(b) Additive cutoff displacement']
    labels = [r'$e^n\lambda_n=\tau_n$', r'$(B_n-e^{\alpha_n})/n$']
    for i, ax in enumerate(axes):
        ax.set_xscale('log')
        ax.plot(n_values, curves[i], color=navy, lw=1.9,
                marker='o', ms=3.5, markevery=mark_indices,
                markerfacecolor='white', markeredgewidth=1.05, zorder=3)
        ax.plot(asym_n, asym_curves[i], color=orange, lw=1.65,
                linestyle=(0, (4.0, 2.5)), zorder=4)
        ax.axhline(limits[i], color=teal, lw=1.4,
                   linestyle=(0, (1.3, 2.2)), zorder=2)
        ax.set_xlim(1.85, 108)
        ax.set_xticks([2, 5, 10, 20, 50, 100])
        ax.xaxis.set_major_formatter(mticker.ScalarFormatter())
        ax.xaxis.set_minor_formatter(mticker.NullFormatter())
        ax.grid(axis='y', color=grid, lw=0.65)
        ax.set_axisbelow(True)
        ax.spines['top'].set_visible(False)
        ax.spines['right'].set_visible(False)
        ax.set_xlabel(r'Laurent index $n$')
        ax.set_ylabel(labels[i], labelpad=7)
        ax.set_title(titles[i], loc='left', pad=11)
        ax.tick_params(which='major', length=3.5, width=0.7)
        ax.tick_params(which='minor', length=2, width=0.5, color='#8A939D')
    axes[0].set_ylim(0.061, 0.274)
    axes[0].yaxis.set_major_locator(mticker.MultipleLocator(0.05))
    axes[0].yaxis.set_major_formatter(mticker.FormatStrFormatter('%.2f'))
    axes[1].set_ylim(0.00227, 0.00585)
    axes[1].yaxis.set_major_locator(mticker.MultipleLocator(0.001))
    axes[1].yaxis.set_major_formatter(mticker.FormatStrFormatter('%.3f'))
    axes[0].annotate(r'$\tau_\infty=0.0757393\ldots$',
                     xy=(3.0, limits[0]), xytext=(3.0, limits[0]+0.010),
                     color=teal, fontsize=8.7)
    axes[1].annotate(r'$\tau_\infty/(4e^2)=0.00256255\ldots$',
                     xy=(2.45, limits[1]), xytext=(2.45, limits[1]-0.00020),
                     color=teal, fontsize=8.7)
    handles = [
        Line2D([0], [0], color=navy, lw=1.9, marker='o', ms=3.5,
               markerfacecolor='white', label='Numerical evaluation'),
        Line2D([0], [0], color=orange, lw=1.65, linestyle=(0, (4.0, 2.5)),
               label=r'Asymptotic expansion ($n\geq8$)'),
        Line2D([0], [0], color=teal, lw=1.4, linestyle=(0, (1.3, 2.2)),
               label=r'Proved limit as $n\to\infty$'),
    ]
    fig.legend(handles=handles, loc='lower center', bbox_to_anchor=(0.51, 0.012),
               ncol=3, frameon=False, fontsize=8.4,
               handlelength=2.8, columnspacing=1.8)
    fig.subplots_adjust(left=0.087, right=0.985, bottom=0.225,
                        top=0.88, wspace=0.32)
    for ext, kwargs in [('pdf', {}), ('png', {'dpi': 300})]:
        target = args.output_dir/f'optimal_barrier_parameters.{ext}'
        fig.savefig(target, bbox_inches='tight', pad_inches=0.055, **kwargs)
        print(target)
    plt.close(fig)


if __name__ == '__main__':
    main()
