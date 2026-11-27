#!/usr/bin/env python3
"""Reproduce numerical illustrations of the proved two-frequency theorem.

These floating-point computations illustrate, and do not replace, the proofs.
Requires mpmath, numpy, scipy and matplotlib. Run from any working directory.
"""
from pathlib import Path
import csv
import json
import math
import mpmath as mp
import numpy as np
from scipy.optimize import brentq, linprog
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]
mp.mp.dps = 85


def bisect(f, a, b, iterations=300):
    fa, fb = f(a), f(b)
    if fa == 0:
        return a
    if fb == 0:
        return b
    assert fa * fb < 0, (fa, fb, a, b)
    for _ in range(iterations):
        c = (a + b) / 2
        fc = f(c)
        if fc == 0:
            return c
        if fa * fc > 0:
            a, fa = c, fc
        else:
            b = c
    return (a + b) / 2


def optimal(r):
    r = mp.mpf(r)
    assert r >= 1
    if r == int(r) and int(r) % 2:
        return dict(r=r, k=(int(r)-1)//2, t=mp.pi/2,
                    T=mp.pi/2, M=mp.nan, P=mp.mpf(1),
                    nodes=[-mp.pi/2, mp.pi/2], weights=[mp.mpf('.5')]*2)
    k = int(mp.floor((r-1)/2))
    s = (-1)**k
    if k == 0:
        t, M = mp.mpf(0), mp.mpf(1)
        T = 2*mp.pi/(1+r)
    else:
        d = lambda u: s*(r*mp.sin(r*u)*mp.cos(u)-mp.cos(r*u)*mp.sin(u))
        t = bisect(d, k*mp.pi/r, (k+mp.mpf('.5'))*mp.pi/r)
        M = s*mp.cos(r*t)/mp.cos(t)
        g = lambda u: M*mp.cos(u)-s*mp.cos(r*u)
        T = bisect(g, mp.pi/2, (2*k+3)*mp.pi/(2*r))
    P = -mp.cos(T)/(mp.cos(t)-mp.cos(T))
    Q = 1-P
    if k == 0:
        nodes, weights = [-T, mp.mpf(0), T], [Q/2, P, Q/2]
    else:
        nodes, weights = [-T, -t, t, T], [Q/2, P/2, P/2, Q/2]
    return dict(r=r, k=k, t=t, T=T, M=M, P=P,
                nodes=nodes, weights=weights)


def fast_width(r):
    k = math.floor((r-1)/2)
    if k == 0:
        return 4*math.pi/(1+r)
    s = (-1)**k
    d = lambda u: s*(r*math.sin(r*u)*math.cos(u)-math.cos(r*u)*math.sin(u))
    t = brentq(d, k*math.pi/r, (k+.5)*math.pi/r, xtol=2e-14)
    M = s*math.cos(r*t)/math.cos(t)
    g = lambda u: M*math.cos(u)-s*math.cos(r*u)
    T = brentq(g, math.pi/2, (2*k+3)*math.pi/(2*r), xtol=2e-14)
    return 2*T


def main():
    (ROOT/'results').mkdir(exist_ok=True)
    (ROOT/'figures').mkdir(exist_ok=True)
    ratios = ['1.01','1.2','1.5','2','2.9','3','3.0001','3.2','4',
              '4.9','5','5.0001','5.6','6.7','7.001','8.5','9.00001','10.2','21.7']
    examples = []
    worst_residual = mp.mpf(0)
    worst_grid_certificate = 0.
    for r in ratios:
        o = optimal(r)
        residual = max(abs(sum(w*mp.exp(1j*f*u) for w,u in zip(o['weights'],o['nodes'])))
                       for f in [mp.mpf(1),o['r']])
        worst_residual = max(worst_residual,residual)
        assert residual < mp.mpf('1e-70')
        assert all(w >= 0 for w in o['weights'])
        assert abs(sum(o['weights'])-1) < mp.mpf('1e-75')
        if not mp.isnan(o['M']):
            grid = np.linspace(-float(o['T']),float(o['T']),20001)
            cert = float(o['M'])*np.cos(grid)-(-1)**o['k']*np.cos(float(o['r'])*grid)
            worst_grid_certificate = min(worst_grid_certificate,float(cert.min()))
            assert cert.min() > -1e-10
        examples.append(dict(r=r, width=mp.nstr(2*o['T'],40),
                             t_star=mp.nstr(o['t'],40),half_width=mp.nstr(o['T'],40),
                             inner_mass=mp.nstr(o['P'],40),
                             nodes=[mp.nstr(v,40) for v in o['nodes']],
                             weights=[mp.nstr(v,40) for v in o['weights']],
                             moment_residual=mp.nstr(residual,8)))

    # Independent discretized convex-hull feasibility checks, away from resonance.
    lp_checks=[]
    for r in [1.2,1.7,2.5,3.2,4.1,5.3,6.4,7.2,8.7,10.2]:
        o=optimal(str(r)); T=float(o['T'])
        outcomes=[]
        for shift in [-.003,.003]:
            grid=np.linspace(0,T+shift,4001)
            A=np.vstack([np.ones_like(grid),np.cos(grid),np.cos(r*grid)])
            res=linprog(np.zeros_like(grid),A_eq=A,b_eq=[1,0,0],
                        bounds=(0,None),method='highs')
            outcomes.append(bool(res.success))
        assert outcomes == [False,True], (r,outcomes)
        lp_checks.append(dict(r=r,below_feasible=outcomes[0],above_feasible=outcomes[1]))

    cusp=[]
    for n in [3,5,7,11]:
        C=(3*mp.pi/(2*n*(n*n-1)))**(mp.mpf(1)/3)
        for e in [2,4,6,9,12,18,24]:
            eps=mp.mpf(10)**(-e); o=optimal(mp.mpf(n)+eps)
            ratio=(2*o['T']-mp.pi)/(4*C*eps**(mp.mpf(1)/3))
            cusp.append(dict(n=n,epsilon=mp.nstr(eps,8),
                             normalized_excess=mp.nstr(ratio,35),
                             inner_mass=mp.nstr(o['P'],35)))
        assert abs(ratio-1)<mp.mpf('1e-14')
        assert abs(o['P']-mp.mpf(2)/3)<mp.mpf('1e-14')

    gamma1=mp.im(mp.zetazero(1)); gamma2=mp.im(mp.zetazero(2))
    o=optimal(gamma2/gamma1)
    shifts=[(u+o['T'])/gamma1 for u in o['nodes']]
    tilted=[w*mp.exp(-u/2) for w,u in zip(o['weights'],shifts)]
    total=sum(tilted); tilted=[w/total for w in tilted]
    zeta_res=max(abs(sum(w*mp.exp((mp.mpf('.5')+1j*g)*u)
                         for w,u in zip(tilted,shifts))) for g in [gamma1,gamma2])
    assert zeta_res<mp.mpf('1e-70')
    zeta=dict(note='Illustrative mpmath zero approximations; not certified zero enclosures.',
              gamma1=mp.nstr(gamma1,40),gamma2=mp.nstr(gamma2,40),
              ratio=mp.nstr(gamma2/gamma1,40),
              log_width=mp.nstr(2*o['T']/gamma1,40),
              dilation_ratio=mp.nstr(mp.exp(2*o['T']/gamma1),40),
              log_shifts=[mp.nstr(v,40) for v in shifts],
              positive_weights=[mp.nstr(v,40) for v in tilted],
              residual=mp.nstr(zeta_res,8))

    out=dict(precision_decimal_digits=mp.mp.dps,
             interpretation='Numerical consistency checks, not computer-assisted proofs.',
             maximum_moment_residual=mp.nstr(worst_residual,8),
             minimum_sampled_dual_certificate=worst_grid_certificate,
             examples=examples,linear_program_checks=lp_checks,cusp=cusp,zeta_example=zeta)
    (ROOT/'results/filter_checks.json').write_text(json.dumps(out,indent=2)+'\n')
    with (ROOT/'results/cusp.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=cusp[0]); w.writeheader(); w.writerows(cusp)

    plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,
                         'axes.spines.top':False,'axes.spines.right':False,
                         'axes.labelcolor':'#24354a','text.color':'#24354a',
                         'xtick.color':'#24354a','ytick.color':'#24354a'})
    fig,axs=plt.subplots(2,1,figsize=(7.2,7.0),gridspec_kw={'height_ratios':[1.18,1]})
    for k in range(5):
        r0=2*k+1
        # More points at the steep right-hand cusp.
        u=np.linspace(.0000003,2,500)
        rs=r0+2*(u/2)**3
        rs=rs[rs<r0+2-1e-7]
        ys=[fast_width(float(r))/math.pi for r in rs]
        axs[0].plot(rs,ys,color='#126f91',lw=2)
    axs[0].scatter([1,3,5,7,9,11],[1]*6,s=24,color='#d47732',zorder=4,label='Odd ratios: exact minimum')
    axs[0].scatter([1],[2],s=35,facecolor='white',edgecolor='#126f91',zorder=5)
    axs[0].set(xlabel='Frequency ratio r',ylabel='Minimum width / π',xlim=(.9,11.1),ylim=(.97,2.06))
    axs[0].set_title('Exact optimum for two prescribed frequencies',loc='left',fontsize=11,pad=12)
    axs[0].legend(frameon=False,loc='upper right',fontsize=8)
    axs[0].grid(alpha=.14)
    for n,color in [(3,'#126f91'),(5,'#d47732'),(7,'#5f8166')]:
        rows=[d for d in cusp if d['n']==n]
        axs[1].semilogx([float(d['epsilon']) for d in rows],
                       [float(d['normalized_excess']) for d in rows],
                       'o-',ms=3,color=color,label=f'n = {n}')
    axs[1].axhline(1,lw=.8,color='#7b8794',ls='--')
    axs[1].set(xlabel='Perturbation ε in r = n + ε',ylabel='(minimum width − π) / (4 Cₙ ε¹ᐟ³)')
    axs[1].set_title('The predicted cube-root coefficient',loc='left',fontsize=11,pad=12)
    axs[1].legend(frameon=False,fontsize=8)
    axs[1].grid(alpha=.14)
    fig.tight_layout(h_pad=2.7)
    fig.savefig(ROOT/'figures/filter_phase_diagram.pdf',bbox_inches='tight')
    fig.savefig(ROOT/'figures/filter_phase_diagram.png',dpi=180,bbox_inches='tight')
    plt.close(fig)
    print(json.dumps({k:out[k] for k in ['precision_decimal_digits','maximum_moment_residual',
                                       'minimum_sampled_dual_certificate']},indent=2))
    print('19 moment/certificate cases; 10 paired LP checks; 28 cusp rows: PASS')
    print(json.dumps(zeta,indent=2))


if __name__=='__main__':
    main()
