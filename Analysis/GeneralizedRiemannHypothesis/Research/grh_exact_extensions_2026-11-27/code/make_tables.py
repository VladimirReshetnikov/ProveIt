"""Recompute paper tables, exact intervals, and the scientific figure."""
from fractions import Fraction as F
from decimal import Decimal, localcontext
from pathlib import Path
import json
import sys
from symplectic_laws import (full_tv,smith_tv,limiting_constant_interval,
                             precision_eigenvalue,survival_infinite,u,R,qpower)

ROOT=Path(__file__).resolve().parents[1]
if hasattr(sys,'set_int_max_str_digits'):
    sys.set_int_max_str_digits(200000)


def decimal(x,digits=55):
    with localcontext() as ctx:
        ctx.prec=digits
        return str(Decimal(x.numerator)/Decimal(x.denominator))


def info(x):
    return {'exact':str(x),'decimal':decimal(x)}


def main():
    data={'finite':[],'limiting':[],'precision_checks':[]}
    for q in (2,3,4,5):
        for n in (2,4,8,20):
            data['finite'].append({'q':q,'n':n,'smith_tv':info(smith_tv(q,n)),
                                  'full_tv':{str(h):info(full_tv(q,n,h))
                                             for h in (1,2,3,None)}})
        for h in (1,2,3,None):
            lo,hi=limiting_constant_interval(q,h,12,140)
            data['limiting'].append({'q':q,'precision':str(h),
                                    'lower':info(lo),'upper':info(hi),
                                    'width':decimal(hi-lo)})
    for q,n in ((2,4),(2,20),(3,4),(3,20)):
        for h in range(1,8):
            gap=full_tv(q,n,None)-full_tv(q,n,h)
            # The theorem's explicit matching lower bound.
            finf2=qpower(q,-1)*survival_infinite(q,2)
            lower=u(q,n,2)*R(q,n,2)*(1-finf2)*qpower(q,-5*h)
            upper=qpower(q,-5*h)
            assert 0 < lower <= gap <= upper
            if n==4:
                assert gap==lower
            data['precision_checks'].append({'q':q,'n':n,'precision':h,
                                            'gap':info(gap),'lower':info(lower),'upper':info(upper)})
    (ROOT/'results'/'tables_and_certificates.json').write_text(json.dumps(data,indent=2)+'\n')
    lines=[r'\begin{tabular}{rrrrr}',r'\toprule',
           r'$q$ & $n$ & Smith: every precision & Full matrix: one digit & Full matrix: all digits\\',
           r'\midrule']
    for q,n in ((2,4),(2,8),(2,20),(3,4),(3,20)):
        lines.append(f'{q} & {n} & {float(smith_tv(q,n)):.11g} & '+
                     f'{float(full_tv(q,n,1)):.11g} & {float(full_tv(q,n,None)):.11g}'+r'\\')
    lines.extend([r'\bottomrule',r'\end{tabular}'])
    (ROOT/'results'/'finite_table.tex').write_text('\n'.join(lines)+'\n')
    lines=[r'\begin{tabular}{rll}',r'\toprule',r'$q$ & $\delta_{q,1}$ & $\delta_{q,\infty}$\\',r'\midrule']
    for q in (2,3,4,5):
        lo1,hi1=limiting_constant_interval(q,1,12,140)
        loi,hii=limiting_constant_interval(q,None,12,140)
        lines.append(f'{q} & {decimal(lo1,20)} & {decimal(loi,20)}'+r'\\')
    lines.extend([r'\bottomrule',r'\end{tabular}'])
    (ROOT/'results'/'limit_table.tex').write_text('\n'.join(lines)+'\n')
    print('Exact tables and certified intervals written.')
    try:
        import matplotlib
        matplotlib.use('Agg')
        import matplotlib.pyplot as plt
    except ImportError:
        print('matplotlib unavailable; exact tables remain complete.')
        return
    plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False,
                         'savefig.bbox':'tight','font.family':'DejaVu Sans'})
    fig,axes=plt.subplots(1,2,figsize=(10.8,3.7),layout='constrained')
    ns=list(range(2,32,2))
    axes[0].semilogy(ns,[float(full_tv(2,n,None)) for n in ns],color='#142d4e',lw=2.3,label='Full matrix, all digits')
    axes[0].semilogy(ns,[float(full_tv(2,n,1)) for n in ns],color='#8193aa',lw=1.8,ls='--',label='Full matrix, first digit')
    axes[0].semilogy(ns,[float(smith_tv(2,n)) for n in ns],color='#b25931',lw=2.3,marker='o',ms=3,label='Entire Smith form, any precision')
    axes[0].set(xlabel='Visible matrix size n (residue field q = 2)',ylabel='Total variation distance',title='The invariant factors hide a persistent difference')
    axes[0].legend(fontsize=8,loc='lower left')
    axes[0].grid(axis='y',alpha=.18)
    hs=list(range(1,8))
    gaps=[float(full_tv(2,20,None)-full_tv(2,20,h)) for h in hs]
    axes[1].semilogy(hs,gaps,color='#142d4e',lw=2.3,marker='o',label='Exact unobserved full-matrix difference')
    axes[1].semilogy(hs,[2**(-5*h) for h in hs],color='#b25931',lw=1.8,ls='--',label=r'Uniform bound $2^{-5h}$')
    axes[1].set(xlabel='Number h of observed binary digits',ylabel=r'$\Delta_{20,\infty}-\Delta_{20,h}$',title='Extra full-matrix information has exponent five')
    axes[1].legend(fontsize=8,loc='upper right')
    axes[1].grid(axis='y',alpha=.18)
    fig.savefig(ROOT/'figures'/'precision_separation.pdf')
    fig.savefig(ROOT/'figures'/'precision_separation.png',dpi=180)
    plt.close(fig)
    print('Figure written; no simulated data used.')


if __name__=='__main__':
    main()
