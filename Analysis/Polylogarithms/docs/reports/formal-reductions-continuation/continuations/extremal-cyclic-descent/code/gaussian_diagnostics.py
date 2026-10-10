#!/usr/bin/env python3
"""Independent floating-point checks and publication figures.

These are diagnostics, not certificates. The exact maximum certificate is
replayed by certify_gaussian_envelope.py, without these dependencies.
"""
from pathlib import Path
from math import comb
import json
import numpy as np
import mpmath as mp
from scipy.special import roots_genlaguerre, roots_jacobi
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT=Path(__file__).resolve().parents[1]
mp.mp.dps=80


def beta(w):
    return mp.dirichlet(w,[0,1,0,-1])


def envelope(w):
    return beta(w)+mp.power(2,-w)*mp.altzeta(w)


def gaussian_euler(a,b,N=220):
    a,b=mp.mpf(a),mp.mpf(b)
    total=mp.mpf(0)
    harmonic=mp.mpf(0)
    weights=2**N-1
    for j in range(N):
        if j:
            harmonic += mp.power(2*j-1,-b)+mp.power(2*j,-b)
        term=harmonic*mp.power(2*j+1,-a)
        total += (-1)**j*term*weights/mp.mpf(2**N)
        if j+1<N:
            weights -= comb(N,j+1)
    return -total


def gaussian_quadrature(a,b,order=120):
    w=a+b
    r,rw=roots_genlaguerre(order,w-1)
    # Jacobi recurrence has a removable 0/0 at a+b=1; SciPy selects
    # the correct limiting value internally. Reject nonfinite output.
    with np.errstate(invalid="ignore"):
        z,vw=roots_jacobi(order,b-1,a-1)
    assert np.all(np.isfinite(z)) and np.all(np.isfinite(vw))
    v=(z+1)/2
    vw=vw/vw.sum()
    rw=rw/rw.sum()
    x=np.exp(-np.outer(v,r))
    y=np.exp(-r)[None,:]
    K=x*(x+y)/((1+x*x)*(1+y*y))
    return float(vw@K@rw)


def inverse_approx(x,terms):
    alpha=mp.log(2); lam=mp.log(mp.mpf(3)/2)/alpha
    mu=mp.log(mp.mpf(5)/2)/alpha
    values=[-x**lam/alpha,-x/alpha,
            -(lam+mp.mpf('.5'))*x**(2*lam)/alpha,
            x**mu/alpha,-(lam+1)*x**(lam+1)/alpha,
            -(3*lam+1)*(3*lam+2)*x**(3*lam)/(6*alpha)]
    return mp.log(1/x)/alpha+sum(values[:terms])


def main():
    cases=[('.1','.9'),('.5','.5'),('.9','.1'),
           ('.25','1.75'),('1','1'),('1.5','.5'),
           ('.5','3.5'),('2','2'),('3.5','.5')]
    checks=[]
    for a,b in cases:
        e=gaussian_euler(a,b)
        q=gaussian_quadrature(float(a),float(b))
        checks.append({'a':a,'b':b,'minus_g_euler':mp.nstr(e,55),
                       'minus_g_gauss_quadrature':q,
                       'absolute_discrepancy':float(abs(e-q))})
    # A direct Mellin derivative avoids removable-singularity differentiation.
    cp1=mp.quad(lambda r:(1+mp.exp(-r))/(2*mp.cosh(r))*(mp.log(r)+mp.euler),
                [0,1,4,mp.inf])
    inv=[]
    for xtext in ['0.01','0.0001','0.000001','0.00000001']:
        x=mp.mpf(xtext)
        start=mp.log(1/x)/mp.log(2)
        exact=mp.findroot(lambda w:envelope(w)-1-x,(start-mp.mpf('.1'),start))
        inv.append({'x':xtext,'root':mp.nstr(exact,55),
                    'errors_by_number_of_corrections':
                      {str(j):mp.nstr(abs(inverse_approx(x,j)-exact),30)
                       for j in [0,1,2,3,4,5,6]}})
    report={'status':'floating-point diagnostics, not rigorous enclosures',
            'mpmath_decimal_precision':mp.mp.dps,'gaussian_checks':checks,
            'C_prime_1_direct_integral':mp.nstr(cp1,60),
            'inverse_checks':inv}
    (ROOT/'results'/'gaussian_diagnostics.json').write_text(json.dumps(report,indent=2)+'\n')

    plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,
                         'axes.spines.top':False,'axes.spines.right':False,
                         'axes.titleweight':'bold','savefig.dpi':200})
    fig,axes=plt.subplots(1,2,figsize=(10.4,3.8),layout='constrained')
    grid=np.linspace(.02,6,240)
    values=np.array([float(envelope(mp.mpf(float(w)))) for w in grid])
    star=1.3022165871012412; maximum=1.1365611033395096
    axes[0].plot(grid,values,color='#173d69',lw=2)
    axes[0].axhline(1,color='#a0a8b2',ls=':',lw=1)
    axes[0].scatter([star],[maximum],color='#b24936',s=32,zorder=4)
    axes[0].annotate('Unique maximum\n(1.3022166, 1.1365611)',
                     xy=(star,maximum),xytext=(2.45,1.133),
                     arrowprops={'arrowstyle':'-','color':'#b24936'},fontsize=9)
    axes[0].set(xlabel='Total order w',ylabel='C(w)',
                title='Sharp envelope of −2 Im F at i',ylim=(.997,1.153))
    agrid=np.linspace(.001,.999,120)
    critical=np.array([2*gaussian_quadrature(a,1-a,100) for a in agrid])
    axes[1].plot(agrid,critical,color='#236b62',lw=2)
    axes[1].scatter([0,1],[np.pi/4+np.log(2)/2,np.pi/2-1],
                    facecolor='white',edgecolor='#236b62',s=40,zorder=4)
    axes[1].set(xlabel='Outer order a; inner order b = 1 − a',
                ylabel='−2 Im F at i',title='Resolved critical-line conjecture',
                xlim=(-.02,1.02))
    for ax in axes:
        ax.grid(alpha=.16)
    fig.savefig(ROOT/'figures'/'gaussian_envelope.pdf')
    fig.savefig(ROOT/'figures'/'gaussian_envelope.png')
    plt.close(fig)
    print(json.dumps({'gaussian_checks':len(checks),
          'max_quadrature_discrepancy':max(c['absolute_discrepancy'] for c in checks),
          'inverse_checks':len(inv),'figures':['gaussian_envelope.pdf','gaussian_envelope.png']},indent=2))


if __name__=='__main__':
    main()
