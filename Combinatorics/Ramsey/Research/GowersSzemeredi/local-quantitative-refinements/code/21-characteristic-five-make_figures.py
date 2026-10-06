#!/usr/bin/env python3
"""Publication figures from exact formulas; Decimal avoids cancellation.

Only matplotlib is an external dependency.  No numerical optimizer is used.
The convergence plot evaluates the explicit fixed-phase, fixed-leading-
amplitude model, not the full moving maximizing branch.
"""
from decimal import Decimal as D, localcontext
from pathlib import Path
import csv
import math
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]
FIGURES = ROOT / 'figures'
DATA = ROOT / 'data'


def model(delta, t):
    with localcontext() as ctx:
        ctx.prec = 90
        two, three = D(2), D(3)
        c5 = two**(D(3)/4)/3
        beta = two**(D(1)/4)/6
        u = delta*t
        b = beta*u*u/delta
        target = u**8
        lo, hi = D(0), u*u
        for _ in range(330):
            x = (lo+hi)/2
            value = 8*x**4+16*x**3*b*b+48*x*x*b**4+16*x*b**6+8*b**8
            if value < target:
                lo = x
            else:
                hi = x
        x = (lo+hi)/2  # rho squared
        quartic = 6*two.sqrt()*delta**4*u**4
        q = (delta**8+24*delta**4*(x*x+b**4)
             +16*delta**3*x*x*b+96*delta*delta*x*x*b*b
             +48*delta*delta*x*b**4+32*delta*x*x*b**3+target)
        sixth = (q-delta**8-quartic)/(delta*delta*u**6)
        eighth = (q-delta**8-quartic-c5*delta*delta*u**6)/u**8
        return sixth, eighth, c5


def main():
    FIGURES.mkdir(exist_ok=True)
    DATA.mkdir(exist_ok=True)
    plt.rcParams.update({
        'font.family':'DejaVu Serif', 'font.size':10,
        'axes.spines.top':False, 'axes.spines.right':False,
        'axes.labelsize':10, 'axes.titlesize':11,
        'pdf.fonttype':42, 'figure.dpi':160,
    })
    ts = [10**(-4+i*(math.log10(.30)+4)/159) for i in range(160)]
    results = [model(D('.4'), D(str(t))) for t in ts]
    sixth = [float(r[0]) for r in results]
    eighth = [float(r[1]) for r in results]
    c5 = float(results[0][2])
    assert abs(sixth[0]-c5) < 3e-8
    assert abs(eighth[0]-20/9) < 1e-6
    with (DATA/'coefficient_convergence.csv').open('w', newline='') as stream:
        writer = csv.writer(stream)
        writer.writerow(['t_u_over_delta','sixth_normalized_correction','eighth_normalized_correction'])
        for t, r in zip(ts, results):
            writer.writerow([format(t,'.17g'),str(r[0]),str(r[1])])
    fig, axes = plt.subplots(1,2,figsize=(9.4,3.5), layout='constrained')
    for ax in axes:
        ax.set_xscale('log')
        ax.set_xlabel(r'$t=u/\delta$')
        ax.grid(True, color='#d8dce2', linewidth=.5, alpha=.7)
        ax.set_axisbelow(True)
    axes[0].plot(ts, sixth, color='#204f7a', linewidth=2.1, label='Exact model')
    axes[0].axhline(c5, color='#ad6126', linewidth=1.5, linestyle='--', label=r'$2^{3/4}/3$')
    axes[0].set_title('Sixth-order coefficient')
    axes[0].set_ylabel(r'$(Q-\delta^8-6\sqrt{2}\,\delta^4u^4)/(\delta^2u^6)$')
    axes[0].legend(frameon=False, loc='upper left')
    axes[1].plot(ts, eighth, color='#204f7a', linewidth=2.1, label='Exact model')
    axes[1].axhline(20/9, color='#ad6126', linewidth=1.5, linestyle='--', label=r'$20/9$')
    axes[1].set_title('Eighth-order coefficient')
    axes[1].set_ylabel(r'$(Q-\delta^8-6\sqrt{2}\,\delta^4u^4-C_5\delta^2u^6)/u^8$')
    axes[1].legend(frameon=False, loc='upper left')
    fig.savefig(FIGURES/'coefficient_convergence.pdf')
    fig.savefig(FIGURES/'coefficient_convergence.png',dpi=200)
    plt.close(fig)
    # The phase envelope is an exact elementary formula.
    thetas = [-math.pi+2*math.pi*i/240 for i in range(241)]
    phis = [math.pi*i/160 for i in range(161)]
    values = [[max(math.cos(theta),0)**2/(1+math.cos(phi)**2)
               for theta in thetas] for phi in phis]
    fig, ax = plt.subplots(figsize=(8.5,3.5),layout='constrained')
    im=ax.imshow(values,origin='lower',aspect='auto',extent=(-math.pi,math.pi,0,math.pi),
                 cmap='cividis',vmin=0,vmax=1,interpolation='bilinear')
    ax.set_xlabel(r'$\theta=2\arg a_\xi-\arg a_{2\xi}$')
    ax.set_ylabel(r'$\phi=3\arg a_\xi+\arg a_{2\xi}$')
    ax.set_xticks([-math.pi,-math.pi/2,0,math.pi/2,math.pi],
                 [r'$-\pi$',r'$-\pi/2$','0',r'$\pi/2$',r'$\pi$'])
    ax.set_yticks([0,math.pi/2,math.pi],['0',r'$\pi/2$',r'$\pi$'])
    ax.plot([0],[math.pi/2],'o',color='white',markeredgecolor='black',markersize=6)
    ax.set_title(r'Sharp phase factor: $(\cos\theta)_+^2/(1+\cos^2\phi)$')
    fig.colorbar(im,ax=ax,label=r'Fraction of the sharp coefficient $C_5$')
    fig.savefig(FIGURES/'phase_envelope.pdf')
    fig.savefig(FIGURES/'phase_envelope.png',dpi=200)
    plt.close(fig)
    print('PASS: 90-digit model evaluation and coefficient limits.')
    print('Figures and convergence data written.')


if __name__ == '__main__':
    main()
