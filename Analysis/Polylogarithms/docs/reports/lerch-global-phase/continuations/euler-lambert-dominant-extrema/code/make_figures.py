#!/usr/bin/env python3
"""Rebuild the article's static research figures from the supplied data.

Every sampled curve is labeled according to its role: exact finite root
isolation, numerical diagnostic, or proven limiting formula. The script
uses no network access. It writes both PDF and PNG figures.
"""
import argparse
import json
from pathlib import Path
import numpy as np
import mpmath as mp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from verify_diagonal_inverse import stirling_polynomials

ROOT=Path(__file__).resolve().parents[1]
FIG=ROOT/'figures'
DATA=ROOT/'data'
SAMPLES=DATA/'figure_samples.json'
INK='#15324c'; TEAL='#146b72'; AMBER='#bd7727'; RED='#a44253'; GRAY='#77828d'
COLORS=[TEAL,AMBER,RED]

def read(name):
    return json.loads((DATA/name).read_text())

def finish(fig,name):
    fig.savefig(FIG/(name+'.pdf'),bbox_inches='tight',
                metadata={'Creator':'ProveIt research continuation','CreationDate':None})
    fig.savefig(FIG/(name+'.png'),dpi=220,bbox_inches='tight')
    plt.close(fig)

def style(ax):
    ax.spines[['top','right']].set_visible(False)
    ax.grid(True,alpha=.17,linewidth=.6)
    ax.tick_params(labelsize=9)

def angle_for_L(L):
    lo,hi=mp.mpf(0),mp.pi
    for _ in range(160):
        t=(lo+hi)/2
        if 1-t*mp.cot(t)+mp.log(t/mp.sin(t))<L:
            lo=t
        else:
            hi=t
    return (lo+hi)/2

def main():
    global FIG, DATA, SAMPLES
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data-dir',type=Path,default=DATA)
    parser.add_argument('--output-dir',type=Path,default=FIG)
    parser.add_argument('--samples-output',type=Path,default=SAMPLES)
    args=parser.parse_args()
    DATA=args.data_dir.resolve(); FIG=args.output_dir.resolve()
    SAMPLES=args.samples_output.resolve()
    FIG.mkdir(parents=True,exist_ok=True)
    SAMPLES.parent.mkdir(parents=True,exist_ok=True)
    plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,
                         'axes.labelcolor':INK,'text.color':INK,
                         'axes.edgecolor':'#9ca6ad','axes.titleweight':'bold',
                         'axes.titlesize':11,'legend.fontsize':8,
                         'figure.constrained_layout.use':True})
    samples={'status':'figure diagnostics and evaluations of exact limiting formulas'}

    # Order-averaged axis optimization; no finite-N globality inferred.
    d=read('axis_large_n_diagnostics.json')
    rows=d['rows']; n=np.array([r['N'] for r in rows])
    fig,axes=plt.subplots(1,2,figsize=(7.2,3.15))
    axes[0].semilogx(n,[float(r['scaled_excess']) for r in rows],'o-',color=TEAL,lw=1.4,ms=4)
    axes[0].axhline(1,color=GRAY,ls='--',lw=1)
    axes[0].set(xlabel='Truncation index $N$',ylabel=r'$(C_N^{\rm ax}-1)/(cN^{-p})$',
                title='Leading Euler correction')
    axes[1].semilogx(n,[float(r['center_shift']) for r in rows],'o-',color=AMBER,lw=1.4,ms=4)
    axes[1].axhline(0,color=GRAY,ls='--',lw=1)
    axes[1].set(xlabel='Truncation index $N$',ylabel=r'$b_N-\widehat b_N$',title='Optimizing inner order')
    for ax in axes:style(ax)
    finish(fig,'euler_axis_asymptotics')

    # Pointwise kernel stationary candidates and their limiting expansion.
    d=read('kernel_diagnostics.json'); rows=d['rows']; lim=d['limit']
    n=np.array([r['N'] for r in rows]); minf=float(lim['M']); kap=float(lim['kappa'])
    fig,axes=plt.subplots(1,2,figsize=(7.2,3.15))
    axes[0].semilogx(n,[float(r['stationary_value']) for r in rows],'o-',color=TEAL,ms=4,lw=1.4)
    axes[0].axhline(minf,color=GRAY,ls='--',lw=1,label=r'$M_\infty$')
    axes[0].set(xlabel='$N$',ylabel='Stationary kernel value',title='Pointwise kernel extrema')
    axes[0].legend(frameon=False)
    axes[1].semilogx(n,[float(r['N_times_excess_over_limit']) for r in rows],'o-',color=AMBER,ms=4,lw=1.4)
    axes[1].axhline(kap,color=GRAY,ls='--',lw=1,label=r'$\kappa_\infty$')
    axes[1].set(xlabel='$N$',ylabel=r'$N(M-M_\infty)$',title='First reciprocal-index term')
    axes[1].legend(frameon=False)
    for ax in axes:style(ax)
    finish(fig,'kernel_limit')

    # Harmonic velocity trace: an independent coefficient recurrence.
    mp.mp.dps=200
    A=mp.mpf(2); L=mp.log(A); theta=angle_for_L(L)
    a=1-theta*mp.cot(theta); u=a+1j*theta; radius=mp.exp(a); chi=mp.sqrt(-2*u)
    chi1=chi*(-mp.mpf(3)/8+u/12+3/(8*u))
    v=[mp.mpf(0),-L/A]
    for n in range(1,240):
        conv=mp.fsum(v[j]*v[n-j] for j in range(1,n))
        v.append(((n+1-n*L)*v[n]+mp.mpf(n)*conv/2)/(A*(n+1)))
    ns=np.arange(40,241)
    z=[]; err0=[]; err1=[]; trace=[]
    for n0 in ns:
        n=int(n0)
        zz=mp.sqrt(mp.pi)*radius**n*mp.mpf(n)**mp.mpf('1.5')*v[n]
        model0=mp.re(chi*mp.exp(-1j*n*theta))
        model1=mp.re((chi+chi1/n)*mp.exp(-1j*n*theta))
        z.append(float(zz));err0.append(float(n*abs(zz-model0)))
        err1.append(float(n*n*abs(zz-model1)))
        trace.append({'n':n,'normalized_velocity':mp.nstr(zz,24),
                      'n_times_leading_error':mp.nstr(n*abs(zz-model0),20),
                      'n2_times_corrected_error':mp.nstr(n*n*abs(zz-model1),20)})
    samples['velocity_trace_A2']=trace
    fig,axes=plt.subplots(1,2,figsize=(7.2,3.2))
    dense=np.linspace(40,85,1600)
    curve=complex(chi)*np.exp(-1j*dense*float(theta))
    axes[0].plot(dense,np.real(curve),color=GRAY,lw=.9,label='Leading cosine')
    mask=ns<=85
    axes[0].scatter(ns[mask],np.array(z)[mask],s=13,color=TEAL,zorder=3,label='Coefficient recurrence')
    axes[0].set(xlabel='Diagonal index $n$',ylabel=r'$\sqrt{\pi} R^n n^{3/2}v_n(2)$',title='Oscillatory zero velocities')
    axes[0].legend(frameon=False,loc='upper center',bbox_to_anchor=(.5,-.19),ncol=1)
    axes[1].plot(ns,err0,color=TEAL,lw=.8,label=r'$n\,|Z_n-Z_n^{(0)}|$')
    axes[1].plot(ns,err1,color=AMBER,lw=.8,label=r'$n^2|Z_n-Z_n^{(1)}|$')
    axes[1].set(xlabel='Diagonal index $n$',ylabel='Scaled absolute model error',title='Additive asymptotic errors')
    axes[1].legend(frameon=False,loc='upper center',bbox_to_anchor=(.5,-.19))
    for ax in axes:style(ax)
    finish(fig,'harmonic_velocity_asymptotics')

    # Bulk CDF and hard endpoint. Finite CDF roots have exact rational isolation.
    rootdata=read('bulk_root_examples.json')
    t=np.linspace(.003,np.pi-.01,2400)
    LL=1-t/np.tan(t)+np.log(t/np.sin(t))
    fig,axes=plt.subplots(1,2,figsize=(7.2,3.3))
    axes[0].plot(LL,t/np.pi,color=INK,lw=1.6,label='Limiting CDF')
    for color,row in zip(COLORS,rootdata['rows']):
        n=row['n'];rr=np.array([float(r['midpoint']) for r in row['positive_roots']])
        xx=np.r_[rr[0]*.5,rr,rr[-1]*1.3]
        yy=np.r_[0,np.arange(1,n)/(n-1),1]
        axes[0].step(xx,yy,where='post',lw=1,color=color,label=f'$n={n}$',alpha=.9)
    axes[0].set(xscale='log',xlim=(.002,90),ylim=(-.02,1.025),xlabel='Logarithmic root coordinate $L$',
                ylabel='Fraction of positive roots',title='An explicit bulk zero law')
    axes[0].legend(frameon=False,loc='lower right')
    x=np.linspace(0,64,400)
    bessel=np.array([-float(mp.sqrt(2*xx)*mp.besselj(1,mp.sqrt(2*xx))) for xx in x])
    axes[1].plot(x,bessel,color=INK,lw=1.6,label=r'$-\sqrt{2x}\,J_1(\sqrt{2x})$')
    polys=stirling_polynomials(60)
    for color,n in zip(COLORS,[12,30,60]):
        cf=np.array([float(c)*n**(2-2*j) for j,c in enumerate(polys[n])])
        axes[1].plot(x,np.polynomial.polynomial.polyval(x,cf),color=color,lw=1,ls='--',label=f'$n={n}$')
    axes[1].set(xlabel='Small-root scale $x=n^2L$',ylabel=r'$n^2p_n(x/n^2)$',title='The Bessel endpoint limit')
    axes[1].legend(frameon=False,loc='lower left')
    for ax in axes:style(ax)
    finish(fig,'lambert_bulk_and_bessel')

    # Exact-index phase conjecture diagnostics; these do not fix the index in a proof.
    quant=[]
    mp.mp.dps=60
    for row in rootdata['rows']:
        n=row['n']
        for j in [n//5,n//2,4*n//5]:
            LL=mp.mpf(row['positive_roots'][j-1]['midpoint'])
            th=angle_for_L(LL);uu=1-th*mp.cot(th)+1j*th;cc=mp.sqrt(-2*uu)
            diff=n*th-mp.arg(cc)-mp.pi*(j+mp.mpf('.5'))
            corr=mp.im(-mp.mpf(3)/8+uu/12+3/(8*uu))/n
            quant.append({'n':n,'j':j,'phase_offset':mp.nstr(diff,24),
                          'proposed_first_correction':mp.nstr(corr,24),
                          'n2_times_corrected_offset':mp.nstr(n*n*(diff-corr),24)})
    samples['bulk_quantization_conjecture_diagnostics']=quant
    samples['Bessel_first_constant']=mp.nstr(mp.besseljzero(1,1)**2/2,40)

    # Largest-root expansion at fixed k and decreasing root index j=1.
    edge=read('cohen_edge_checks.json')['numerical']
    rows=[r for r in edge['rows'] if r['j_decreasing_index']==1]
    ks=sorted({r['k'] for r in rows})
    fig,axes=plt.subplots(1,2,figsize=(7.2,3.2))
    c0=float(edge['Cohen_C0_decimal'])
    for color,k in zip(COLORS,ks):
        group=[r for r in rows if r['k']==k];nn=[r['n'] for r in group]
        axes[0].semilogx(nn,[float(r['n_times_root_minus_leading_terms']) for r in group],
                        'o-',color=color,lw=1.2,ms=3.5,label=f'$k={k}$')
        axes[1].semilogx(nn,[float(r['n2_times_prediction_error']) for r in group],
                        'o-',color=color,lw=1.2,ms=3.5,label=f'$k={k}$')
        axes[1].axhline(float(group[0]['predicted_Cohen_C1_k']),color=color,lw=.8,ls='--')
    axes[0].axhline(c0,color=GRAY,ls='--',lw=1)
    axes[0].set(xlabel='Polynomial index $n$',ylabel=r'$n(X_{n,k,1}-n-k+1-\log n-\gamma)$',
                title='A common first zeta coefficient')
    axes[1].set(xlabel='Polynomial index $n$',ylabel='Second scaled root correction',
                title='The next coefficient depends on $k$')
    for ax in axes:style(ax);ax.legend(frameon=False)
    finish(fig,'cohen_extreme_root_coefficients')
    SAMPLES.write_text(json.dumps(samples,indent=2)+'\n')
    print('Rebuilt five figure pairs and their additional numerical samples.')

if __name__=='__main__':
    main()
