#!/usr/bin/env python3
"""Two-panel scientific figure for the uniform harmonic-depth saddle.

The smooth leading curves are evaluated from the theorem's explicit saddle
formula. All Mellin quadrature values and error diagnostics are read from
the supplied JSON. The plot does not manufacture quadrature observations or
claim interval error bounds.

Usage:
    python code/plot_harmonic_saddle.py
    python code/plot_harmonic_saddle.py --data /path/to/uniform_saddle.json

Requires Python 3, NumPy, SciPy, and Matplotlib. Outputs PNG, vector PDF,
vector SVG, the plotted data CSV, and provenance metadata next to the script
unless --out is specified. No high-precision quadrature is rerun.
"""
from pathlib import Path
import argparse
import csv
import hashlib
import json
import math

import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.ticker import LogFormatterMathtext, NullLocator
from scipy.optimize import brentq


ROOT = Path(__file__).resolve().parents[1]
HERE = ROOT / "figures"
DEPTHS = (25, 100, 400)
COLORS = {25: '#D55E00', 100: '#0072B2', 400: '#009E73'}
INK = '#243447'
GRAY = '#66737F'


def q_minus_one(t):
    """log(1+t)/t - 1, avoiding loss of its small correction."""
    if t < 0.01:
        # The last term is below 1e-33 at the branch point.
        total = 0.0
        for k in range(16, 0, -1):
            total = (-1.0)**k / (k+1) + t*total
        return t*total
    return math.log1p(t)/t - 1.0


def w_and_derivative(x):
    t = math.exp(-x)
    qm1 = q_minus_one(t)
    w = 1.0/((1.0+t)*(1.0+qm1))
    # Exact identity: w'(x) = -(log(1+t)/t - 1) w(x)^2.
    return w, -qm1*w*w, qm1, t


def log1p_minus_x(x):
    if abs(x) < 0.01:
        total = 0.0
        for k in range(16, 1, -1):
            total = (-1.0)**(k+1)/k + x*total
        return x*x*total
    return math.log1p(x)-x


def leading_log(alpha, h, a=0.5):
    p = alpha*h
    lo = p/(h+a)
    hi = p/(h/(2.0*math.log(2.0))+a)
    def equation(x):
        return x*(h*w_and_derivative(x)[0]+a)-p
    x = brentq(equation, lo, hi, xtol=1e-14, rtol=1e-14)
    w, wp, qm1, t = w_and_derivative(x)
    theta = h/(h*w+a)
    B_minus_one = theta*x*wp
    # Stable form of theta*(1-w).
    delta = theta*(t+(1.0+t)*qm1)*w
    exponent = p*log1p_minus_x(delta)+h*math.log1p(qm1)
    return exponent-math.log1p(t)-0.5*math.log1p(B_minus_one)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data', type=Path, default=ROOT/'results'/'uniform_saddle.json')
    parser.add_argument('--out', type=Path, default=HERE)
    args = parser.parse_args()
    payload = args.data.read_bytes()
    data = json.loads(payload)
    rows = [r for r in data['cases']
            if float(r['h']) in DEPTHS and float(r['a']) == 0.5
            and 0.2 <= float(r['alpha']) <= 20.0]
    assert len(rows) == 18, 'Expected the six diagnostic parameters at each depth.'
    grouped = {h: sorted([r for r in rows if float(r['h']) == h],
                         key=lambda r: float(r['alpha'])) for h in DEPTHS}
    assert all(len(v) == 6 for v in grouped.values())
    max_formula_relative_discrepancy = max(
        abs(leading_log(float(r['alpha']),float(r['h']))/float(r['log_A'])-1.0)
        for r in rows)
    assert max_formula_relative_discrepancy < 2e-12
    error_min = min(abs(float(r['corrected_relative_error'])) for r in rows)
    assert error_min > 1e-15, 'A requested plotted point is too small for this chosen diagnostic view.'

    plt.rcParams.update({
        'font.family': 'DejaVu Sans', 'font.size': 9,
        'mathtext.fontset': 'dejavusans',
        'axes.labelcolor': INK, 'axes.edgecolor': '#AAB4BD',
        'axes.titleweight': 'bold', 'axes.titlesize': 10,
        'text.color': INK, 'xtick.color': GRAY, 'ytick.color': GRAY,
        'xtick.labelsize': 8.2, 'ytick.labelsize': 8.2,
        'axes.spines.top': False, 'axes.spines.right': False,
        'axes.linewidth': 0.7, 'pdf.fonttype': 42, 'ps.fonttype': 42,
        'svg.fonttype': 'none', 'savefig.facecolor': 'white',
    })
    # Sized for a 6.5--7.2 inch manuscript width, with readable type after
    # modest scaling. This is not a slide with oversized physical width.
    fig, (left, right) = plt.subplots(1, 2, figsize=(7.2, 4.4))
    fig.subplots_adjust(left=0.088, right=0.985, bottom=0.27, top=0.82, wspace=0.31)
    fig.suptitle('Uniform harmonic-depth saddle', x=0.088, y=0.975,
                 ha='left', va='top', fontsize=13, fontweight='bold')
    fig.text(0.985, 0.965, r'Shift $a=1/2$  ·  $h\in\{25,100,400\}$',
             ha='right', va='top', fontsize=8.5, color=GRAY)
    left.set_title('A   Normalization across the range', loc='left', pad=12)
    right.set_title('B   Sampled relative errors', loc='left', pad=12)

    alpha_grid = np.linspace(0.2, 20.0, 560)
    export_rows = []
    for h in DEPTHS:
        color = COLORS[h]
        y = np.array([-leading_log(float(alpha),h) for alpha in alpha_grid])
        left.plot(alpha_grid, y, color=color, lw=1.9, zorder=2)
        sample = grouped[h]
        alpha = np.array([float(r['alpha']) for r in sample])
        log_R = np.array([-float(r['log_R']) for r in sample])
        e0 = np.array([abs(float(r['leading_relative_error'])) for r in sample])
        e1 = np.array([abs(float(r['corrected_relative_error'])) for r in sample])
        left.scatter(alpha, log_R, s=30, facecolors='white', edgecolors=color,
                     linewidths=1.2, zorder=4)
        right.plot(alpha, e0, color=color, lw=1.2, marker='o', ms=4.6,
                   markeredgecolor='white', markeredgewidth=0.45, zorder=3)
        right.plot(alpha, e1, color=color, lw=1.2, linestyle=(0,(4,2.5)),
                   marker='s', ms=4.3, markerfacecolor='white',
                   markeredgewidth=1.05, zorder=3)
        for row in sample:
            export_rows.append({
                'h': h, 'a': 0.5, 'alpha': row['alpha'], 'p': row['p'],
                'minus_log_R': str(-float(row['log_R'])),
                'minus_log_A': str(-float(row['log_A'])),
                'abs_leading_relative_error': str(abs(float(row['leading_relative_error']))),
                'abs_corrected_relative_error': str(abs(float(row['corrected_relative_error']))),
            })

    for ax in (left,right):
        ax.set_yscale('log')
        ax.set_xlim(0.0,20.4)
        ax.set_xticks([0,5,10,15,20])
        ax.set_xlabel(r'Ratio of exponent to depth $\alpha=p/h$', labelpad=8)
        ax.yaxis.set_major_formatter(LogFormatterMathtext())
        ax.yaxis.set_minor_locator(NullLocator())
        ax.grid(axis='y', color='#E4E9ED', linewidth=0.7)
        ax.set_axisbelow(True)
        ax.tick_params(axis='both', which='major', length=3, width=0.6)
    left.set_ylim(1e-8, 240)
    left.set_yticks([1e-8,1e-6,1e-4,1e-2,1,1e2])
    left.set_ylabel(r'$-\log R_{p,h}(1/2)$', labelpad=8)
    left.axhline(0.5, color='#ADB6BE', lw=0.8, linestyle=(0,(2,3)), zorder=1)
    left.text(19.8,0.72,r'Transition level $1/2$',ha='right',va='bottom',
              fontsize=7.5,color=GRAY)
    left.legend(handles=[
        Line2D([0],[0], color=INK, lw=1.8, label=r'Leading formula $\mathcal{A}$'),
        Line2D([0],[0], color=INK, lw=0, marker='o', markerfacecolor='white',
               ms=4.6, label=r'Mellin quadrature $R$'),
    ],loc='lower left',bbox_to_anchor=(0.015,0.02),frameon=True,
       facecolor='white',edgecolor='none',framealpha=0.92,
       fontsize=7.8,handlelength=2.2,borderpad=0.6,labelspacing=0.65)

    right.set_ylim(4e-13,1e-2)
    right.set_yticks([1e-12,1e-10,1e-8,1e-6,1e-4,1e-2])
    right.set_ylabel('Absolute relative error', labelpad=8)
    right.legend(handles=[
        Line2D([0],[0],color=INK,lw=1.15,marker='o',ms=4.5,
               label='Leading approximation'),
        Line2D([0],[0],color=INK,lw=1.15,linestyle=(0,(4,2.5)),marker='s',
               markerfacecolor='white',ms=4.2,
               label='First correction'),
    ],loc='upper right',bbox_to_anchor=(1.005,0.995),frameon=True,
       facecolor='white',edgecolor='none',framealpha=0.94,
       fontsize=7.2,handlelength=2.0,borderpad=0.45,labelspacing=0.75)

    fig.legend(handles=[Line2D([0],[0],color=COLORS[h],lw=2.2,label=rf'$h={h}$')
                        for h in DEPTHS],
               loc='lower center',bbox_to_anchor=(0.535,0.073),ncol=3,
               frameon=False,fontsize=9,columnspacing=2.6,handlelength=2.1)
    dps=data['working_decimal_digits']
    fig.text(0.088,0.025,f'{dps}-digit quadrature; diagnostic comparisons.',
             ha='left',va='bottom',fontsize=7.2,color=GRAY)
    fig.text(0.985,0.025,'Uniform remainder proved analytically.',
             ha='right',va='bottom',fontsize=7.2,color=GRAY)

    args.out.mkdir(parents=True,exist_ok=True)
    stem=args.out/'uniform_harmonic_saddle'
    fig.savefig(stem.with_suffix('.png'),dpi=240)
    fig.savefig(stem.with_suffix('.pdf'),metadata={'Title':'Uniform harmonic-depth saddle',
                    'Subject':'Explicit leading formula and numerical quadrature diagnostics'})
    fig.savefig(stem.with_suffix('.svg'))
    plt.close(fig)
    with (args.out/'uniform_harmonic_saddle_points.csv').open('w',newline='') as stream:
        writer=csv.DictWriter(stream,fieldnames=export_rows[0].keys())
        writer.writeheader();writer.writerows(export_rows)
    ratios=[abs(float(r['leading_relative_error'])/float(r['corrected_relative_error'])) for r in rows]
    metadata={
        'source_file':args.data.name,
        'source_sha256':hashlib.sha256(payload).hexdigest(),
        'source_status':data['status'], 'quadrature_working_decimal_digits':dps,
        'selected_depths':list(DEPTHS),'shift':0.5,'selected_points':len(rows),
        'curve_alpha_range':[0.2,20.0],'curve_points_per_depth':len(alpha_grid),
        'curve_formula':'Explicit leading moving-saddle approximation; no curve-grid quadrature',
        'curve_float_relative_discrepancy_against_source_log_A':max_formula_relative_discrepancy,
        'minimum_displayed_corrected_error':error_min,
        'minimum_correction_improvement_factor':min(ratios),
        'maximum_correction_improvement_factor':max(ratios),
        'caveat':'Quadrature values and plotted errors are numerical diagnostics, not interval certificates.'}
    (args.out/'uniform_harmonic_saddle_metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
    print(json.dumps(metadata,indent=2))


if __name__=='__main__':main()
