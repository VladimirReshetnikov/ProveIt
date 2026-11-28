#!/usr/bin/env python3
"""Reproduce constants, analytic cross-checks, discrete saddles, and figures.

Python 3 with mpmath, numpy, scipy, and matplotlib. Run from any directory.
Numerical checks are not a formal proof or interval-arithmetic certification.
The discrete calculation is an exact-product saddle calculation, not a claim
that the finite-u saddle rate equals the logarithm of a probability.
"""
from pathlib import Path
import json
import math
import platform
import sys
import argparse
import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data"
FIGURES = ROOT / "figures"
mp.mp.dps = 70


def fmt(x, digits=50):
    return mp.nstr(mp.re(x), digits)


def bisect(f, lo, hi, tol=mp.mpf('1e-58')):
    lo, hi = mp.mpf(lo), mp.mpf(hi)
    flo, fhi = f(lo), f(hi)
    if flo == 0:
        return lo
    if fhi == 0:
        return hi
    if flo*fhi > 0:
        raise ValueError(f"Not bracketed: {lo}, {hi}, {flo}, {fhi}")
    for _ in range(240):
        mid = (lo+hi)/2
        fm = f(mid)
        if fm == 0 or hi-lo < tol*(1+abs(mid)):
            return mid
        if flo*fm > 0:
            lo, flo = mid, fm
        else:
            hi, fhi = mid, fm
    raise RuntimeError("Bisection did not converge")


def lr2(c, a, upper=False):
    """Analytic integrals on [0,c] or [c,infinity], alpha=1,p=2."""
    c, a = mp.mpf(c), mp.mpf(a)
    if not upper:
        return mp.atan(c/mp.sqrt(a))/mp.sqrt(a)
    if a > 0:
        return mp.atan(mp.sqrt(a)/c)/mp.sqrt(a)
    if a == 0:
        return 1/c
    return mp.atanh(mp.sqrt(-a)/c)/mp.sqrt(-a)


def quantile_constants(tau):
    tau=mp.mpf(tau)
    k=tau/(1-tau)
    w=bisect(lambda w: mp.atan(mp.sqrt(k)/w)-mp.sqrt(k)*mp.atanh(w),
             mp.mpf('1e-45'), 1-mp.mpf('1e-45'))
    star=2*mp.atanh(w)/(mp.pi*(1-tau)*w)
    A=w*w/k
    B=-w*w
    K=mp.log((1+A)/(1+B))
    return dict(tau=tau, w=w, A=A, B=B, c0=mp.tan(mp.pi*tau/2),
                cstar=star, K=K)


def saddle2(c, constants):
    c=mp.mpf(c)
    tau=constants['tau']
    C=mp.pi/2
    if c >= constants['cstar']:
        a=c*c*constants['A']; b=c*c*constants['B']
        lam=mp.mpf(0)
        total=constants['cstar']/c
        rate=c*constants['K']-C
        phase='interior'
    else:
        lo=mp.mpf('1e-50'); hi=max(mp.mpf(4),c*c)
        while lr2(c,hi)>tau*C:
            hi*=2
        a=bisect(lambda a:lr2(c,a)-tau*C,lo,hi)
        lo=-c*c*(1-mp.mpf('1e-50')); hi=max(mp.mpf(4),c*c)
        while lr2(c,hi,True)>(1-tau)*C:
            hi*=2
        b=bisect(lambda b:lr2(c,b,True)-(1-tau)*C,lo,hi)
        lam=tau*a+(1-tau)*b
        total=mp.mpf(1)
        rate=c*mp.log((c*c+a)/(c*c+b))+C*(lam-1)
        phase='boundary'
    return dict(c=c,a=a,b=b,lam=lam,total=total,rate=rate,phase=phase)


def quadrature_checks(constants):
    """Use quadrature independently of the closed integral formulas."""
    out=[]
    for d in constants:
        c=(d['c0']+d['cstar'])/2
        for c in [c, mp.mpf('1.25')*d['cstar']]:
            s=saddle2(c,d)
            a,b=s['a'],s['b']
            L=mp.quad(lambda r:1/(r*r+a),[0,c])
            R=mp.quad(lambda r:1/(r*r+b),[c,mp.inf])
            F=mp.quad(lambda r:mp.log((r*r+a)/(r*r+1)),[0,c])
            F+=mp.quad(lambda r:mp.log((r*r+b)/(r*r+1)),[c,mp.inf])
            ipb=c*mp.log((c*c+a)/(c*c+b))+2*(a*L+b*R)-mp.pi
            via_dual=F+mp.pi/2-a*L-b*R
            errors=[abs(L-lr2(c,a)),abs(R-lr2(c,b,True)),abs(F-ipb),
                    abs(via_dual-s['rate'])]
            # Infinite-endpoint quadrature loses some digits in cancellation.
            assert max(errors)<mp.mpf('1e-30'),errors
            out.append(dict(tau=fmt(d['tau']),c=fmt(c),phase=s['phase'],
                quadrature_errors=[fmt(x) for x in errors]))
    return out


def general_checks():
    """Check the alpha,p integration identity at independent arbitrary rates."""
    out=[]
    parameters=[('0.75','2','1.4','1.3','-0.4'),
                ('1','2','2','2.2','-2'),
                ('2','3','1.3','2','-0.5'),
                ('1.5','4','0.8','0.7','0.3')]
    for alpha,p,c,a,b in parameters:
        alpha,p,c,a,b=map(mp.mpf,(alpha,p,c,a,b))
        nu=lambda r:alpha*r**(alpha-1)
        L=mp.quad(lambda r:nu(r)/(r**p+a),[0,c])
        R=mp.quad(lambda r:nu(r)/(r**p+b),[c,mp.inf])
        C=alpha*mp.pi/(p*mp.sin(mp.pi*alpha/p))
        F=mp.quad(lambda r:nu(r)*mp.log((r**p+a)/(r**p+1)),[0,c])
        F+=mp.quad(lambda r:nu(r)*mp.log((r**p+b)/(r**p+1)),[c,mp.inf])
        rhs=c**alpha*mp.log((c**p+a)/(c**p+b))+(p/alpha)*(a*L+b*R-C)
        err=abs(F-rhs)
        assert err<mp.mpf('1e-20'),err
        out.append(dict(alpha=fmt(alpha),p=fmt(p),c=fmt(c),a=fmt(a),b=fmt(b),
                        integration_by_parts_error=fmt(err)))
    return out


def curvature_checks(d):
    c=d['cstar'];tau=d['tau'];a=c*c*d['A'];b=c*c*d['B']
    U=mp.quad(lambda r:1/(r*r+a)**2,[0,c])
    V=mp.quad(lambda r:1/(r*r+b)**2,[c,mp.inf])
    jump=(mp.pi/(2*c))**2*(tau*tau/U+(1-tau)**2/V)
    # Compute the active-side curvature by implicit differentiation, separately.
    aprime=1/((c*c+a)*U)
    bprime=-1/((c*c+b)*V)
    direct=(2*c+aprime)/(c*c+a)-(2*c+bprime)/(c*c+b)
    assert abs(direct-jump)<mp.mpf('1e-50')
    rate_at_star=c*d['K']-mp.pi/2
    rate_boundary=c*mp.log((c*c+a)/(c*c+b))+mp.pi/2*(tau*a+(1-tau)*b-1)
    assert abs(rate_at_star-rate_boundary)<mp.mpf('1e-50')
    c0=d['c0']
    U0=mp.quad(lambda r:1/(1+r*r)**2,[0,c0])
    V0=mp.quad(lambda r:1/(1+r*r)**2,[c0,mp.inf])
    curv0=(1/U0+1/V0)/(1+c0*c0)**2
    return dict(tau=fmt(tau),transition_rate=fmt(rate_at_star),
                slope_at_transition=fmt(d['K']),left_second_derivative=fmt(jump),
                right_second_derivative='0',independent_curvature_error=fmt(abs(direct-jump)),
                matching_rate_error=fmt(abs(rate_at_star-rate_boundary)),
                typical_cutoff_curvature=fmt(curv0))


def discrete_tail_sum(m,u,b):
    """u*sum_{j=m}^infinity 1/(j^2+b*u^2), from digamma."""
    m,u,b=mp.mpf(m),mp.mpf(u),mp.mpf(b)
    if b == 0:
        return u*mp.polygamma(1,m)
    if b > 0:
        z=u*mp.sqrt(b)
        ans=u*(mp.digamma(m+1j*z)-mp.digamma(m-1j*z))/(2j*z)
    else:
        z=u*mp.sqrt(-b)
        ans=u*(mp.digamma(m+z)-mp.digamma(m-z))/(2*z)
    return mp.re(ans)


def discrete_low_sum(m,u,a):
    """Use the all-spectrum coth identity minus the digamma tail."""
    z=mp.mpf(u)*mp.sqrt(a)
    full=u*(mp.pi*z*mp.coth(mp.pi*z)-1)/(2*z*z)
    return full-discrete_tail_sum(m,u,a)


def discrete_tail_logproduct(m,u,b):
    if b == 0:
        return mp.mpf(0)
    if b > 0:
        z=mp.mpf(u)*mp.sqrt(b)
        val=2*mp.loggamma(m)-mp.loggamma(m+1j*z)-mp.loggamma(m-1j*z)
    else:
        z=mp.mpf(u)*mp.sqrt(-b)
        val=2*mp.loggamma(m)-mp.loggamma(m+z)-mp.loggamma(m-z)
    return mp.re(val)


def discrete_saddle(u,c,d):
    """Exact product-cumulant saddle for gamma_j=j, n=u integer."""
    c=mp.mpf(c);u=int(u);J=int(mp.floor(c*u));m=J+1
    tau=d['tau'];k=tau/(1-tau)
    mu=(mp.pi*mp.coth(mp.pi*u)-mp.mpf(1)/u)/2
    L=lambda a:discrete_low_sum(m,u,a)
    R=lambda b:discrete_tail_sum(m,u,b)
    amin=mp.mpf('1e-30');amax=(mp.mpf(m)/u)**2/k*(1-mp.mpf('1e-30'))
    ai=bisect(lambda a:(1-tau)*L(a)-tau*R(-k*a),amin,amax,tol=mp.mpf('1e-42'))
    bi=-k*ai;si=L(ai)+R(bi)
    if si<=mu:
        a,b=ai,bi;phase='interior'
    else:
        hi=max(4,c*c)
        while L(hi)>tau*mu:
            hi*=2
        a=bisect(lambda a:L(a)-tau*mu,amin,hi,tol=mp.mpf('1e-42'))
        blo=-(mp.mpf(m)/u)**2*(1-mp.mpf('1e-30'))
        hi=max(4,c*c)
        while R(hi)>(1-tau)*mu:
            hi*=2
        b=bisect(lambda b:R(b)-(1-tau)*mu,blo,hi,tol=mp.mpf('1e-42'))
        phase='boundary'
    l,r=L(a),R(b)
    lowlog=mp.fsum(mp.log1p(a*u*u/(j*j)) for j in range(1,J+1))
    taillog=discrete_tail_logproduct(m,u,b)
    baseline=mp.log(mp.sinh(mp.pi*u)/(mp.pi*u))
    F=(lowlog+taillog-baseline)/u
    rate=F+mu-a*l-b*r
    continuum=saddle2(c,d)
    # Independent finite-sum check on the digamma/coth formula.
    directlow=u*mp.fsum(1/(j*j+a*u*u) for j in range(1,J+1))
    assert abs(directlow-l)<mp.mpf('1e-50')
    assert abs((1-tau)*l-tau*r)<mp.mpf('1e-37')
    return dict(u=u,c=fmt(c),J=J,phase=phase,a=fmt(a),b=fmt(b),
                exact_discrete_saddle_rate=fmt(rate),continuum_rate=fmt(continuum['rate']),
                rate_error=fmt(rate-continuum['rate']),
                exact_discrete_saddle_total_ratio=fmt((l+r)/mu),
                continuum_total_ratio=fmt(continuum['total']),
                finite_sum_identity_error=fmt(abs(directlow-l)))


def figures(d):
    import numpy as np
    import scipy.optimize as so
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.ticker import MaxNLocator
    star=float(d['cstar']);K=float(d['K']);w=float(d['w'])
    def Rint(c,b):
        if abs(b)<1e-12:return 1/c
        if b>0:return math.atan(math.sqrt(b)/c)/math.sqrt(b)
        return math.atanh(math.sqrt(-b)/c)/math.sqrt(-b)
    def solve(c):
        if c>=star:
            a=(c*w)**2;b=-a
            return a,b,c*K-math.pi/2,star/c
        a=so.brentq(lambda a:math.atan(c/math.sqrt(a))/math.sqrt(a)-math.pi/4,1e-12,100)
        b=so.brentq(lambda b:Rint(c,b)-math.pi/4,-c*c*(1-1e-12),100)
        rate=c*math.log((c*c+a)/(c*c+b))+math.pi/2*((a+b)/2-1)
        return a,b,rate,1.
    plt.rcParams.update({'font.family':'DejaVu Sans','font.size':9,
        'axes.spines.top':False,'axes.spines.right':False,'axes.linewidth':.7,
        'savefig.bbox':'tight','pdf.fonttype':42,'ps.fonttype':42})
    cs=np.linspace(1,3.2,361)
    results=np.array([solve(c) for c in cs])
    fig,axs=plt.subplots(1,2,figsize=(8.5,3.25))
    colors=['#096778','#B3552D']
    for ax,vals,color,title,ylabel in zip(axs,[results[:,2],results[:,3]],colors,
        ['Exponential cost of a late median','Total mass under the additional rare event'],
        [r'Rate $\mathcal{R}_{1/2}(c)$',r'Limit of $X/x$']):
        ax.plot(cs,vals,color=color,lw=2.2)
        ax.axvline(star,color='#687078',ls='--',lw=1)
        ax.set_xlabel(r'Cutoff $c$ in $H_{1/2}>cu$')
        ax.set_ylabel(ylabel)
        ax.set_title(title,fontsize=10,pad=11)
        ax.grid(axis='y',alpha=.16)
        ax.set_xlim(1,3.2)
        ax.xaxis.set_major_locator(MaxNLocator(5))
    axs[0].annotate(r'$c_*=1.62612\ldots$',xy=(star,star*K-math.pi/2),
        xytext=(1.12,1.65),fontsize=9,arrowprops={'arrowstyle':'-','color':'#687078','lw':.8})
    axs[0].text(2.03,2.0,r'$\mathcal{R}(c)=Kc-\pi/2$',color=colors[0],fontsize=10)
    axs[1].set_ylim(.44,1.06)
    axs[1].text(1.10,.92,r'$X/x\to1$',color=colors[1],fontsize=10)
    axs[1].text(2.02,.88,r'$X/x\to c_*/c$',color=colors[1],fontsize=10)
    fig.tight_layout(w_pad=2.5)
    for ext in ['pdf','png']:
        fig.savefig(FIGURES/f'phase_transition.{ext}',dpi=220)
    plt.close(fig)
    fig,ax=plt.subplots(figsize=(7.25,3.7))
    rs=np.linspace(0,6,600)
    ax.plot(rs,2/np.pi*np.arctan(rs),ls='--',color='#7B8289',lw=1.7,
            label='Typical profile without the late-median event')
    for c,col in zip([1.2,star,2.5],['#126D82','#703B82','#C26032']):
        a,b,rate,total=solve(c)
        vals=[]
        for r in rs:
            if r<=c:
                z=math.atan(r/math.sqrt(a))/math.sqrt(a)
            else:
                z=math.atan(c/math.sqrt(a))/math.sqrt(a)+Rint(c,b)-Rint(r,b)
            vals.append(2/math.pi*z)
        label=f'c = {c:.5f}' if c==star else f'c = {c:g}'
        if c==star: label+=r' ($c_*$)'
        ax.plot(rs,vals,color=col,lw=2,label=label)
        ax.axvline(c,color=col,lw=.65,alpha=.20)
    ax.set_xlabel(r'Scaled spectral height $r=\gamma/u$')
    ax.set_ylabel(r'Cumulative contribution divided by $x$')
    ax.set_title('The limiting mass profile after a late-median event',pad=12)
    ax.set_xlim(0,6);ax.set_ylim(0,1.03)
    ax.grid(axis='y',alpha=.16)
    ax.legend(frameon=False,loc='lower right',fontsize=8.5)
    fig.tight_layout()
    for ext in ['pdf','png']:
        fig.savefig(FIGURES/f'conditional_profiles.{ext}',dpi=220)
    plt.close(fig)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-discrete',action='store_true',help='Skip the exact-product finite-u comparison.')
    parser.add_argument('--skip-figures',action='store_true')
    args=parser.parse_args()
    DATA.mkdir(parents=True,exist_ok=True);FIGURES.mkdir(parents=True,exist_ok=True)
    constants=[quantile_constants(t) for t in ['0.2','0.5','0.8']]
    median=constants[1]
    print('Computing 70-digit constants and independent quadrature checks...',flush=True)
    curvature=[curvature_checks(d) for d in constants]
    exact_curv0=4*mp.pi/(mp.pi**2-4)
    assert abs(mp.mpf(curvature[1]['typical_cutoff_curvature'])-exact_curv0)<mp.mpf('1e-48')
    result=dict(
        description='Numerical cross-checks; not interval certification or a formal proof.',
        precision_decimal_digits=mp.mp.dps,
        runtime=dict(python=platform.python_version(),mpmath=mp.__version__),
        constants=[{key:fmt(v) for key,v in d.items()} for d in constants],
        quadrature=quadrature_checks(constants),
        general_integration_by_parts=general_checks(),
        curvature=curvature,
        median_typical_curvature_exact_formula='4*pi/(pi^2-4)',
        median_typical_curvature=fmt(exact_curv0),
        median_rates=[{key:(val if key=='phase' else fmt(val)) for key,val in
            saddle2(c,median).items()} for c in [mp.mpf('1.05'),mp.mpf('1.2'),mp.mpf('1.4'),
            mp.mpf('1.6'),median['cstar'],mp.mpf(2),mp.mpf(3),mp.mpf(5)]],
        discrete_saddles=[])
    if not args.skip_discrete:
        print('Comparing exact gamma_j=j product saddles at u=25,50,100,200...',flush=True)
        for c in ['1.2','1.5','2','3']:
            for u in [25,50,100,200]:
                row=discrete_saddle(u,c,median)
                result['discrete_saddles'].append(row)
                print(f"  c={c}, u={u}: rate={float(row['exact_discrete_saddle_rate']):.10f}, "
                      f"limit={float(row['continuum_rate']):.10f}",flush=True)
    if not args.skip_figures:
        figures(median)
    (DATA/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    lines=['VERIFICATION SUMMARY','All numerical assertions passed.',
        'Precision: 70 decimal digits (mpmath). Numerical values are not certified intervals.',
        '',f"Median w*: {fmt(median['w'])}",f"Median c*: {fmt(median['cstar'])}",
        f"Median K: {fmt(median['K'])}",f"Median transition rate: {curvature[1]['transition_rate']}",
        f"Median transition left curvature: {curvature[1]['left_second_derivative']}",
        f"Median transition right curvature: 0",f"Median typical curvature 4*pi/(pi^2-4): {fmt(exact_curv0)}",
        '', 'Checks: closed integrals against quadrature; integration by parts for four general (alpha,p) pairs;',
        'rate matching at transition; independent implicit-differentiation curvature; typical CLT curvature;',
        'exact digamma/coth finite-sum identities and gamma-product discrete saddles.',
        '', 'DISCRETE SADDLE COMPARISON (gamma_j=j; this is not a finite-u probability estimate)',
        'c\tu\tsaddle rate\tcontinuum rate\tsaddle X/x\tlimit X/x']
    for row in result['discrete_saddles']:
        lines.append('\t'.join([row['c'],str(row['u'])]+[f"{float(row[k]):.12g}" for k in
            ['exact_discrete_saddle_rate','continuum_rate','exact_discrete_saddle_total_ratio','continuum_total_ratio']]))
    (DATA/'verification.txt').write_text('\n'.join(lines)+'\n')
    print(f'Saved {DATA/"verification.json"}',flush=True)
    print(f'Saved {DATA/"verification.txt"}',flush=True)

if __name__=='__main__':
    main()
