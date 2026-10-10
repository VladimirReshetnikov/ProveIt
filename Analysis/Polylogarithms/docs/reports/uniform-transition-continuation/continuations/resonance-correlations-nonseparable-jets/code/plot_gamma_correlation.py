"""Reproduce the publication figure for periodic log-Gamma correlations.

Run from any directory:
    python /path/to/plot_gamma_correlation.py

Requires the sibling gamma_correlation.py, mpmath, NumPy, and matplotlib.
The plotted values use the proved convergent expansion, symmetry about
a=1/2, and exact analytic endpoint limits. No fitted or conjectural
curve is used. PDF output retains vector paths and embedded TrueType
fonts; PNG is a 300 dpi preview.
"""

from pathlib import Path
import json

import mpmath as mp
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.ticker import FixedLocator, FuncFormatter

from gamma_correlation import (
    squared_increment, centered_second_moment, maximum_increment,
)


def main():
    out = Path(__file__).resolve().parents[1] / 'figures'
    out.mkdir(exist_ok=True)
    mp.mp.dps = 50
    terms = 64

    # Resolve the logarithmic endpoint cusp while retaining a smooth
    # polyline throughout the interval. Evaluate only the left half;
    # the right half is its exact reflected set of samples.
    half = np.unique(np.concatenate([
        np.linspace(0.0, 0.5, 351),
        np.geomspace(1e-8, 0.035, 95),
    ]))
    increments = []
    tail_bounds = []
    for a in half:
        result = squared_increment(mp.mpf(str(a)), terms=terms)
        increments.append(float(result.value))
        tail_bounds.append(result.tail_bound)
    increments = np.array(increments)
    # Exact endpoint and independently evaluated extremum, up to final
    # conversion to the doubles required by matplotlib.
    increments[0] = 0.0
    maximum = maximum_increment()
    increments[-1] = float(maximum)
    x = np.concatenate([half, 1-half[-2::-1]])
    S = np.concatenate([increments, increments[-2::-1]])
    R0 = mp.log(2*mp.pi)**2/4 + centered_second_moment()
    R = float(R0)-S/2
    minimum = R0-maximum/2
    R[0] = R[-1] = float(R0)

    plt.rcParams.update({
        'font.family': 'STIXGeneral',
        'mathtext.fontset': 'stix',
        'font.size': 10.5,
        'axes.labelsize': 11.5,
        'axes.titlesize': 11,
        'xtick.labelsize': 9.5,
        'ytick.labelsize': 9.5,
        'axes.linewidth': 0.75,
        'pdf.fonttype': 42,
        'ps.fonttype': 42,
        'savefig.facecolor': 'white',
        'figure.facecolor': 'white',
    })
    blue = '#215B85'
    rust = '#A24D36'
    grey = '#64717A'

    fig, axes = plt.subplots(1, 2, figsize=(7.4, 3.45))
    fig.subplots_adjust(left=0.079, right=0.987, bottom=0.175,
                        top=0.885, wspace=0.27)
    for ax in axes:
        ax.spines['top'].set_visible(False)
        ax.spines['right'].set_visible(False)
        ax.spines['left'].set_color('#64717A')
        ax.spines['bottom'].set_color('#64717A')
        ax.set_xlim(0, 1)
        ax.xaxis.set_major_locator(FixedLocator([0, .25, .5, .75, 1]))
        ax.xaxis.set_major_formatter(FuncFormatter(
            lambda v, _: {0:'0', .25:r'$\frac{1}{4}$',
                          .5:r'$\frac{1}{2}$', .75:r'$\frac{3}{4}$',
                          1:'1'}.get(v, '')
        ))
        ax.tick_params(axis='both', direction='out', length=3.3,
                       width=.7, color='#64717A', pad=4)
        ax.set_xlabel(r'Shift $a$', labelpad=4)
        ax.axvline(.5, color='#AEB8BF', linestyle=(0, (2.4, 3.5)),
                   linewidth=.75, zorder=0)
        ax.grid(axis='y', color='#E3E8EC', linewidth=.6, zorder=0)
        ax.set_axisbelow(True)

    ax = axes[0]
    ax.plot(x, S, color=blue, linewidth=1.95)
    ax.scatter([0, .5, 1], [0, float(maximum), 0],
               s=[15, 24, 15], color=blue, zorder=4, clip_on=False)
    ax.set_ylim(0, 3.12)
    ax.set_yticks([0, 1, 2, 3])
    ax.set_ylabel(r'$S(a)$', rotation=0, labelpad=14)
    ax.set_title('(a) Squared translation increment', loc='left', pad=12)
    ax.annotate(r'$\max S = 2.68072249\ldots$',
                xy=(.5, float(maximum)), xytext=(.5, 3.015),
                ha='center', va='center', fontsize=10,
                color=blue,
                arrowprops={'arrowstyle':'-', 'color':grey,
                            'lw':.7, 'shrinkA':3, 'shrinkB':5})
    ax.text(.5, .20, 'Strictly concave', transform=ax.transAxes,
            ha='center', va='center', color=blue, fontsize=10.3)

    ax = axes[1]
    ax.plot(x, R, color=rust, linewidth=1.95)
    ax.scatter([0, .5, 1], [float(R0), float(minimum), float(R0)],
               s=[15, 24, 15], color=rust, zorder=4, clip_on=False)
    ax.set_ylim(.15, 2.08)
    ax.set_yticks([.5, 1, 1.5, 2])
    ax.set_ylabel(r'$R(a)$', rotation=0, labelpad=14)
    ax.set_title('(b) Autocorrelation', loc='left', pad=12)
    ax.annotate(r'$\min R = 0.52595584\ldots$',
                xy=(.5, float(minimum)), xytext=(.5, .285),
                ha='center', va='center', fontsize=10,
                color=rust,
                arrowprops={'arrowstyle':'-', 'color':grey,
                            'lw':.7, 'shrinkA':3, 'shrinkB':5})
    ax.text(.5, .69, 'Strictly convex', transform=ax.transAxes,
            ha='center', va='center', color=rust, fontsize=10.3)

    pdf = out/'gamma_correlation_figure.pdf'
    png = out/'gamma_correlation_figure.png'
    fig.savefig(pdf, metadata={
        'Title':'Periodic log-Gamma correlation and squared translation increment',
        'Subject':'Proved strict convexity, strict concavity, and unique half-shift extrema',
        'Creator':'plot_gamma_correlation.py with matplotlib',
    })
    fig.savefig(png, dpi=300)
    plt.close(fig)
    metadata = {
        'definition_g':'g(x)=log Gamma(x), extended periodically',
        'S':'integral_0^1 [g({x+a})-g(x)]^2 dx',
        'R':'integral_0^1 g(x)g({x+a}) dx',
        'R0':mp.nstr(R0, 45),
        'S_half':mp.nstr(maximum, 45),
        'R_half':mp.nstr(minimum, 45),
        'working_decimal_digits':mp.mp.dps,
        'last_series_index':terms,
        'number_of_plot_samples':len(x),
        'maximum_analytic_tail_bound':mp.nstr(max(tail_bounds), 12),
        'tail_bound_scope':'Omitted terms only; not interval arithmetic for roundoff.',
        'endpoint_values':'S(0)=S(1)=0; R(0)=R(1)=integral_0^1 logGamma(x)^2 dx.',
        'evaluation':'Convergent odd-zeta expansion; symmetry reduction; exact endpoint limits.',
    }
    (out.parent/'data'/'gamma_correlation_figure_metadata.json').write_text(
        json.dumps(metadata, indent=2)+'\n'
    )
    print(json.dumps({'pdf':str(pdf), 'png':str(png),
                      'metadata':metadata}, indent=2))


if __name__ == '__main__':
    main()
