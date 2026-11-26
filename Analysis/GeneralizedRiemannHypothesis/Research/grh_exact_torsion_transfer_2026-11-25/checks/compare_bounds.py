#!/usr/bin/env python3
"""Reproduce the exact bound table and illustrative log-scale figure.

All CSV/LaTeX table entries use fractions and integer arithmetic, including
the ceiling of the prior expression involving a square root.  The plotted
curves use floating-point approximations and show sufficient UPPER bounds
for an order exponent H; the root order is p**H, not H.
"""
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path
import csv
import json

from verify_exact_torsion import exact_bound, positive_bound


def ceil_sqrt_rational(value: Q) -> int:
    assert value >= 0
    floor_root = isqrt(value.numerator // value.denominator)
    if floor_root * floor_root * value.denominator == value.numerator:
        return floor_root
    return floor_root + 1


def prior_bound(budget: Q, tolerance: Q, h0: int = 2) -> int:
    """The previous report's sufficient bound at p=3, eta=1, n=1.

    ceil((h0+B+delta+1)*(1+2B/(3delta))**(3/2))
    is obtained by squaring the positive expression and taking an exact
    rational square-root ceiling.
    """
    t0 = h0 + budget + tolerance + 1
    factor = 1 + Q(2, 3) * budget / tolerance
    return ceil_sqrt_rational(t0 * t0 * factor * factor * factor)


def main():
    project = Path(__file__).resolve().parents[1]
    data, figures = project/'data', project/'figures'
    data.mkdir(exist_ok=True)
    figures.mkdir(exist_ok=True)
    p, h0, budget = 3, 2, Q(1)
    rows = []
    for delta in (Q(1,2), Q(1,10), Q(1,100), Q(1,1000)):
        old = prior_bound(budget, delta, h0)
        # Exact arithmetic certifies the ceiling, including both strict
        # and non-strict ends, without floating-point square roots.
        t0 = h0 + budget + delta + 1
        P = 1 + Q(2,3)*budget/delta
        square = t0*t0*P*P*P
        assert Q((old-1)**2) < square <= Q(old**2)
        rows.append({
            'delta': str(delta),
            'prior_H': old,
            'refined_positive_H': positive_bound(p,h0,budget,delta),
            'exact_zero_H': exact_bound(p,h0,budget),
        })
    with (data/'bounds.csv').open('w',newline='') as out:
        writer=csv.DictWriter(out,fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    latex = [
        r'\begin{tabular}{rrrr}',
        r'\toprule',
        r'$\delta$ & Prior $H$ & Refined $H_+$ & Exact $H_0$\\',
        r'\midrule',
    ]
    for row in rows:
        latex.append(f"${row['delta']}$ & {row['prior_H']:,} & "
                     f"{row['refined_positive_H']:,} & {row['exact_zero_H']:,}"+r'\\')
    latex += [r'\bottomrule',r'\end{tabular}']
    (data/'bounds_table.tex').write_text('\n'.join(latex)+'\n')

    # Optional plotting dependency, separate from the exact-arithmetic data.
    import numpy as np
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.ticker import LogLocator, NullFormatter
    delta=np.logspace(-4,0,700)
    t0=h0+float(budget)+delta+1
    prior=np.ceil(t0*(1+(2/3)*float(budget)/delta)**1.5)
    kappa=1-1/((p-1)*(t0+1))
    positive=h0+np.ceil(float(budget)*t0/(kappa*delta))
    exact=np.full_like(delta,exact_bound(p,h0,budget))
    plt.rcParams.update({
        'font.family':'DejaVu Sans','font.size':10,
        'axes.labelsize':10,'axes.titlesize':12,
        'legend.fontsize':9,'pdf.fonttype':42,'ps.fonttype':42,
    })
    fig,ax=plt.subplots(figsize=(7.4,4.6),layout='constrained')
    ax.loglog(delta,prior,color='#71819a',linewidth=2,
              label='Prior positive-tolerance bound')
    ax.loglog(delta,positive,color='#21618c',linewidth=2,
              label='Refined positive-tolerance bound')
    ax.loglog(delta,exact,color='#a94535',linewidth=2.3,
              label='Exact specialization (zero tolerance)')
    for row in rows:
        x=float(Q(row['delta']))
        ax.scatter([x],[row['prior_H']],color='#71819a',s=18,zorder=4)
        ax.scatter([x],[row['refined_positive_H']],color='#21618c',s=18,zorder=4)
    ax.set_xlim(1e-4,1)
    ax.set_ylim(5,4e6)
    ax.set_xlabel('Allowed valuation tolerance '+r'$\delta$')
    ax.set_ylabel('Sufficient upper bound for shell exponent '+r'$H$')
    ax.set_title(r'Order-exponent bounds: $p=3$, $h_0=2$, $B=1$',loc='left',pad=12)
    ax.grid(which='major',color='#dbe0e5',linewidth=.7)
    ax.grid(which='minor',axis='y',color='#e9edf0',linewidth=.4,alpha=.65)
    ax.spines[['top','right']].set_visible(False)
    ax.xaxis.set_minor_formatter(NullFormatter())
    ax.yaxis.set_minor_locator(LogLocator(base=10,subs=(2,5)))
    ax.legend(loc='upper right',frameon=True,facecolor='white',edgecolor='#e0e4e8')
    ax.text(.025,.025,'Root order is bounded by '+r'$3^H$'+', not by '+r'$H$'+'.\n'
            'Curves are approximate; tabulated ceilings are exact.',
            transform=ax.transAxes,va='bottom',ha='left',fontsize=8.5,
            bbox={'facecolor':'white','edgecolor':'none','alpha':.93,'pad':5})
    fig.savefig(figures/'order_bounds.pdf',bbox_inches='tight')
    fig.savefig(figures/'order_bounds.png',dpi=200,bbox_inches='tight')
    plt.close(fig)
    print(json.dumps({'parameters':{'p':p,'h0':h0,'B':str(budget)},
                      'exact_table':rows,
                      'files':['data/bounds.csv','data/bounds_table.tex',
                               'figures/order_bounds.pdf','figures/order_bounds.png']},indent=2))


if __name__=='__main__':
    main()
