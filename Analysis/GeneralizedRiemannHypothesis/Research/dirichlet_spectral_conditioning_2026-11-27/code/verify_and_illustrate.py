#!/usr/bin/env python3
"""Reproduce constants and illustrations for the spectral conditioning report.

The proofs are analytic.  Numerical calculations here are checks/illustrations,
not interval-certified proofs.  The conditional simulation uses the explicitly
finite model gamma_j=j, j<=4096; it is NOT a simulation of all zeta zeros.
"""
from __future__ import annotations

import argparse
import json
import math
import platform
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np
import scipy
from scipy.special import lambertw, ndtr

BASE = Path(__file__).resolve().parents[1]
DATA = BASE / "data"
FIG = BASE / "figures"
SEED = 20261127


def profile(c):
    c = np.asarray(c)
    return 2 * np.arctan(c) / np.pi


def clock(c):
    c = np.asarray(c)
    return 2 * (np.arctan(c) + c / (1 + c*c)) / np.pi


def iid_transition(c, theta=1.0):
    return 2*ndtr(np.asarray(c)**2.5 * np.sqrt(theta/(50*np.pi)))-1


def ensemble_transition(v):
    v = np.asarray(v, dtype=float)
    a = -np.log1p(-v)/v
    return 2*(ndtr(np.sqrt(a))-ndtr(np.sqrt((1-v)*a)))


def exact_constants():
    mp.mp.dps = 60
    checks=[]
    for alpha,p in [(1,2),(.7,1.3),(2,3),(.5,2.5)]:
        a, b = mp.mpf(str(alpha)), mp.mpf(str(p))
        c1=a*mp.pi/(b*mp.sin(mp.pi*a/b))
        c2=(1-a/b)*c1
        num1=mp.quad(lambda r:a*r**(a-1)/(1+r**b), [0,1,mp.inf])
        num2=mp.quad(lambda r:a*r**(a-1)/(1+r**b)**2, [0,1,mp.inf])
        err=max(abs(num1-c1),abs(num2-c2))
        assert err<mp.mpf('1e-20'), (alpha,p,err)
        checks.append(dict(alpha=alpha,p=p,C1=str(c1),C2=str(c2),max_abs_error=str(err)))
    v1=mp.mpf('.5')+1/mp.pi
    var=v1*(1-v1)
    assert abs(var-(mp.mpf('.25')-1/mp.pi**2))<mp.mpf('1e-55')
    med=[]
    for ell in [2,4,8,16,32,64]:
        j=lambda c:mp.quad(lambda r:mp.log(r)/(1+r*r),[0,1,c])
        f=lambda c:ell*mp.atan(c)+j(c)-mp.pi*ell/4
        c=mp.findroot(f,(1+mp.catalan/ell,1+3*mp.catalan/ell))
        med.append(dict(ell=ell,c_ell=str(c),first_order=str(1+2*mp.catalan/ell),
                        residual=str(abs(f(c))),scaled_second_order=str(ell**2*(c-1-2*mp.catalan/ell))))
        assert abs(f(c))<mp.mpf('1e-50')
    return dict(integrals=checks,Catalan=str(mp.catalan),V_one=str(v1),
                bridge_variance_at_one=str(var),median_roots=med,
                critical_tv=[dict(c=c,theta=1,limit=float(iid_transition(c))) for c in [.5,1,2,3,4]])


def conditional_finite_simulation(rng, draws):
    rows=[]
    illustrations={}
    n=4096
    gamma=np.arange(1,n+1,dtype=float)
    cuts=np.array([.5,1.,2.])
    for u in [32.,128.]:
        t=u*u
        inv=1/(gamma*gamma+t)
        x=float(inv.sum())
        sigma=float(np.sqrt((inv*inv).sum()))
        end=np.floor(cuts*u).astype(int)
        means=np.array([inv[:k].sum() for k in end])
        variances=np.array([(inv[:k]**2).sum()/sigma**2 for k in end])
        accepted=[]
        for start in range(0,draws,256):
            batch=min(256,draws-start)
            y=rng.exponential(size=(batch,n))*inv
            total=y.sum(axis=1)
            # This rejection rule gives the exact conditional law of the
            # specified finite sum under its original independent exponentials.
            keep=(total<=x)&(np.log(rng.random(batch))<=t*(total-x))
            if np.any(keep):
                yk=y[keep]; sk=total[keep]
                partial=np.stack([yk[:,:k].sum(axis=1) for k in end],axis=1)
                z=(partial-means)/sigma
                slack=t*(x-sk)
                low=t*yk[:,0]
                accepted.append(np.column_stack([z,slack,low,partial/x]))
        a=np.concatenate(accepted)
        cov=np.cov(a[:,:3],rowvar=False)
        limiting=np.minimum.outer(clock(cuts),clock(cuts))-np.outer(clock(cuts),clock(cuts))
        finite=np.minimum.outer(variances,variances)-np.outer(variances,variances)
        rows.append(dict(model="FINITE gamma_j=j, theta=1",n=n,u=u,draws=draws,
            accepted=len(a),acceptance=float(len(a)/draws),x=x,sigma=sigma,
            mean_fraction=a[:,5:].mean(axis=0).tolist(),exact_tilted_mean_fraction=(means/x).tolist(),
            asymptotic_mean_fraction=profile(cuts).tolist(),
            normalized_mean=a[:,:3].mean(axis=0).tolist(),empirical_covariance=cov.tolist(),
            finite_clock_bridge_prediction=finite.tolist(),infinite_limit_covariance=limiting.tolist(),
            slack_mean=float(a[:,3].mean()),slack_variance=float(a[:,3].var(ddof=1)),
            low_coordinate_mean=float(a[:,4].mean()),
            correlations_with_slack=np.corrcoef(a[:,:5],rowvar=False)[:3,3].tolist()))
        illustrations[u]=a
    return rows,illustrations


def synthetic_spectral_points(h):
    """N(T)=floor(T/(2pi)*(log(T/(2pi))-1)) for T>=2pi e.

    This deterministic model has the zeta counting asymptotic, but its points
    are NOT zeta zero ordinates.  The inverse uses the principal Lambert W.
    """
    n=max(0,int(math.floor(h/(2*np.pi)*(math.log(h/(2*np.pi))-1))))
    j=np.arange(1,n+1,dtype=float)
    return 2*np.pi*j/lambertw(j/np.e).real


def product_likelihood_simulation(rng, draws):
    rows=[]
    for u in [1000.,10000.]:
        for c in [1.,2.,3.]:
            h=c*(u**4/math.log(u))**.2
            gamma=synthetic_spectral_points(h)
            eps=(gamma/u)**2
            const=float(np.log1p(eps).sum())
            p_count=q_count=0
            # Evaluate the exact Neyman--Pearson event log(dQ/dP)>0.
            # Use a common-random-number coupling to reduce Monte Carlo noise.
            diffs=[]
            for start in range(0,draws,512):
                batch=min(512,draws-start)
                e=rng.exponential(size=(batch,len(gamma)))
                lp=const-e@eps
                lq=const-(e/(1+eps))@eps
                dp=(lq>0).astype(float)-(lp>0).astype(float)
                diffs.append(dp)
                p_count+=int((lp>0).sum());q_count+=int((lq>0).sum())
            d=np.concatenate(diffs)
            tau2=float(eps@eps)
            log_aff=float(np.log(2*np.sqrt(1+eps)/(2+eps)).sum())
            rows.append(dict(model="SYNTHETIC Riemann-von Mangoldt count, not zeta zeros",
                u=u,c=c,h=h,coordinates=len(gamma),draws=draws,tau_squared=tau2,
                tv_estimate=float(d.mean()),paired_standard_error=float(d.std(ddof=1)/np.sqrt(draws)),
                finite_tau_normal_profile=float(2*ndtr(np.sqrt(tau2)/2)-1),
                asymptotic_c_profile=float(iid_transition(c)),
                exact_hellinger_affinity=float(np.exp(log_aff)),
                unit_rate_event_probability=p_count/draws,tilted_event_probability=q_count/draws))
    return rows


def make_figures(samples, product_rows):
    plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False,
                         'axes.labelcolor':'#233b4d','text.color':'#233b4d',
                         'axes.titleweight':'bold','figure.dpi':160})
    c=np.linspace(0,5,501)
    fig,ax=plt.subplots(1,2,figsize=(10.2,3.7),layout='constrained')
    ax[0].plot(c,profile(c),lw=2.3,label='mean fraction A(c)',color='#167e92')
    ax[0].plot(c,clock(c),lw=2.3,label='variance clock V(c)',color='#cc7a29')
    ax[0].axvline(1,color='#82909b',ls=':',lw=1)
    ax[0].set(xlabel='height / saddle height  c',ylabel='fraction',ylim=(0,1.02),title='Two different spectral profiles')
    ax[0].legend(frameon=False)
    ax[1].plot(c,iid_transition(c),color='#7b4f99',lw=2.3)
    ax[1].set(xlabel='cutoff multiplier  c',ylabel='limiting total-variation distance',
              ylim=(0,1.02),title='Sharp equal-rate gamma transition')
    ax[1].text(.22,.84,r'$h=c(u^4/\log u)^{1/5},\quad \theta=1$',transform=ax[1].transAxes)
    fig.savefig(FIG/'universal_profiles.pdf');fig.savefig(FIG/'universal_profiles.png');plt.close(fig)

    fig,ax=plt.subplots(1,2,figsize=(10.2,3.6),layout='constrained')
    a=samples[128.]
    ax[0].hist(a[:,3],bins=28,density=True,color='#167e92',alpha=.5,label='conditional finite simulation')
    z=np.linspace(0,7,200)
    ax[0].plot(z,np.exp(-z),color='#233b4d',lw=2,label='Exp(1) limit')
    ax[0].set(xlabel=r'$u^2(x-X)$',ylabel='density',title='Gap below the rare-event boundary',xlim=(0,7))
    ax[0].legend(frameon=False,fontsize=8)
    var=.25-1/np.pi**2
    y=np.linspace(-1.6,1.6,250)
    ax[1].hist(a[:,1],bins=28,density=True,color='#cc7a29',alpha=.5,label='conditional finite simulation')
    ax[1].plot(y,np.exp(-y*y/(2*var))/np.sqrt(2*np.pi*var),color='#233b4d',lw=2,label='bridge marginal limit')
    ax[1].set(xlabel=r'$(X(1)-m(1))/\sigma$',ylabel='density',title='Fluctuation at the saddle height')
    ax[1].legend(frameon=False,fontsize=8)
    fig.savefig(FIG/'finite_model_simulation.pdf');fig.savefig(FIG/'finite_model_simulation.png');plt.close(fig)

    fig,ax=plt.subplots(figsize=(6.5,3.7),layout='constrained')
    ax.plot(c[1:],ensemble_transition(clock(c[1:])),lw=2.2,color='#167e92')
    ax.set(xlabel='height / saddle height  c',ylabel='limiting total-variation distance',
           title='Conditioning versus independent tilted coordinates',ylim=(0,1))
    fig.savefig(FIG/'ensemble_transition.pdf');fig.savefig(FIG/'ensemble_transition.png');plt.close(fig)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--draws',type=int,default=50000)
    args=parser.parse_args()
    DATA.mkdir(exist_ok=True);FIG.mkdir(exist_ok=True)
    constants=exact_constants()
    rng=np.random.default_rng(SEED)
    conditional,samples=conditional_finite_simulation(rng,args.draws)
    products=product_likelihood_simulation(rng,args.draws)
    make_figures(samples,products)
    results=dict(status="Analytic theorem supported by numerical illustrations; no numerical proof claim",
        seed=SEED,environment=dict(python=platform.python_version(),numpy=np.__version__,scipy=scipy.__version__,
                                  mpmath=mp.__version__,matplotlib=matplotlib.__version__),
        constants=constants,conditional_finite_simulation=conditional,product_likelihood_simulation=products)
    (DATA/'verification.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(dict(integral_checks=len(constants['integrals']),
         conditional=[dict(u=r['u'],accepted=r['accepted'],slack_mean=r['slack_mean'],
                           low_coordinate_mean=r['low_coordinate_mean']) for r in conditional],
         product_comparisons=[{k:r[k] for k in ['u','c','coordinates','tv_estimate','paired_standard_error',
                              'finite_tau_normal_profile','asymptotic_c_profile']} for r in products]),indent=2))


if __name__=='__main__':
    main()
