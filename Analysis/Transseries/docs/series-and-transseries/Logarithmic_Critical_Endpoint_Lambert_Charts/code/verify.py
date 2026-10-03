#!/usr/bin/env python3
"""Reproduce diagnostics for logarithmic critical countable-action transseries.

Numerical diagnostics are not interval certificates. The FFT coefficient method
has a separate, exact-arithmetic alias bound; floating-point roundoff is checked
against an mpmath recurrence at a small index, not globally certified.
"""
from __future__ import annotations
import argparse
import json
import math
import platform
from pathlib import Path
import numpy as np
import mpmath as mp
import sympy as sy
import scipy
from scipy.optimize import brentq

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'data'
mp.mp.dps = 80
D0 = mp.zeta(3)
D1 = mp.zeta(2)
BC = 1 / D1
H = mp.mpf('1.5')
PHI0 = 1 / mp.sqrt(2 * mp.pi)
G1C = (2-mp.euler-mp.log(2))/4
G2C = mp.mpf(3)/32*((mp.mpf(8)/3-mp.euler-mp.log(2))**2-mp.pi**2/2-mp.mpf(40)/9)


def scales(n: int, beta: mp.mpf) -> tuple[mp.mpf, mp.mpf, mp.mpf]:
    if n <= 0 or beta <= 0:
        raise ValueError('n and beta must be positive')
    arg = -2 * mp.exp(-2 * H) / (n * beta)
    if arg < -1/mp.e:
        raise ValueError('large-scale Lambert branch is not real')
    ell = -mp.lambertw(arg, -1)/2
    a = mp.sqrt(n*beta)
    return a, a*mp.sqrt(ell), ell


def beta_for_lambda(n: int, target: float) -> mp.mpf:
    if target == 0:
        return BC
    b0 = scales(n, BC)[1]
    guess = BC*(1-mp.mpf(target)*b0/n)
    return mp.findroot(lambda z: n*(1-z*D1)/scales(n,z)[1]-target,
                       (guess*mp.mpf('.99'),guess*mp.mpf('1.01')))


def g1_ratio(lam: float) -> mp.mpf:
    l=mp.mpf(lam)
    f=lambda s: mp.exp(-s*s/2)*s*s*(mp.log(s)*mp.cos(l*s)-mp.pi/2*mp.sin(l*s))
    val=mp.quad(f,[0,1,3,8,mp.inf])/(2*mp.pi)
    return val/(mp.exp(-l*l/2)*PHI0)


def fft_mass(n: int, beta: float, cutoff: int|None = None) -> tuple[float,float,int]:
    """e^{-n beta zeta(3)} [t^n] exp(n beta A_M(t)).

    Terms of A above n can be dropped exactly. Sampling radius r=e^{-3/n}
    and period L>=16(n+1) gives alias <=r^L in exact arithmetic, because the
    normalized exponential has nonnegative coefficients of total mass <=1.
    """
    if n < 1 or beta <= 0:
        raise ValueError('invalid n or beta')
    m=n if cutoff is None else min(n,cutoff)
    if m < 1:
        return 0.,0.,0
    length=1 << (16*(n+1)-1).bit_length()
    j=np.arange(1,m+1,dtype=float)
    coeff=np.zeros(length,dtype=float)
    coeff[1:m+1]=n*beta*np.exp(-3*j/n)/j**3
    vals=np.fft.fft(coeff)
    vals=np.exp(vals-n*beta*float(D0))
    ans=np.fft.ifft(vals)[n].real*math.exp(3)
    return float(ans), math.exp(-3*length/n), length


def mp_mass(n: int,beta:mp.mpf,cutoff:int|None=None)->mp.mpf:
    m=n if cutoff is None else min(n,cutoff)
    p=[mp.exp(-n*beta*D0)]+[mp.mpf(0)]*n
    for k in range(1,n+1):
        p[k]=n*beta/k*mp.fsum(p[k-j]/(mp.mpf(j)**2) for j in range(1,min(k,m)+1))
    return p[n]


def symbolic_checks()->dict:
    T,e,c,r0,r1=sy.symbols('T e c r0 r1')
    v1=-2*e*r0/(c*(2-e))
    v2=2*e*(c*r1*(2-e)**2+e*(3*e-10)*r0**2)/(c**2*(e-2)**3)
    V=1+v1*T+v2*T*T
    F=V**2*(1-e*sy.log(V))+(2*e/c)*T*V**3*(r0+r1*T*V)-1
    for k in range(3):
        assert sy.factor(sy.expand(sy.series(F,T,0,3).removeO()).coeff(T,k))==0
    z=sy.symbols('z')
    y=z
    for _ in range(7):
        fun=sum(y**k/(sy.factorial(k)*(k-1)) for k in range(2,8))
        y=sy.series(z*(1-fun),z,0,8).removeO()
    expected=z-z**3/2-z**4/12+sy.Rational(35,72)*z**5+sy.Rational(33,160)*z**6-sy.Rational(1013,1800)*z**7
    assert sy.expand(y-expected)==0
    G=sum(y**k/(sy.factorial(k)*(k-2)) for k in range(3,8))
    Hseries=sy.series(sy.Rational(1,2)+y-y**2/(2*z)-G,z,0,7).removeO()
    Hexpected=(sy.Rational(1,2)+z/2-z**3/6-z**4/48+
               sy.Rational(11,90)*z**5+sy.Rational(119,2880)*z**6)
    assert sy.expand(Hseries-Hexpected)==0
    Jseries=sy.series(sum(y**k/(sy.factorial(k)*k) for k in range(1,7)),z,0,6).removeO()
    Jexpected=z+z**2/4-sy.Rational(4,9)*z**3-sy.Rational(31,96)*z**4+sy.Rational(653,1800)*z**5
    assert sy.expand(Jseries-Jexpected)==0
    # Exact coefficient identity in a noncritical rational test model.
    q=sy.symbols('q'); N=6
    A=sum(q**j/sy.Integer(j)**3 for j in range(1,N+1))
    U=sy.Integer(0)
    for n in range(1,N+1):
        rhs=sum(q**j/sy.Integer(j)**3*sy.series(sy.exp(j*U),q,0,n-j+1).removeO()
                for j in range(1,n+1))
        un=sy.expand(rhs).coeff(q,n)
        # Coefficients of exp(n A) via the exponential recurrence.
        b=[sy.Integer(1)]
        for k in range(1,n+1):
            b.append(sy.Rational(n,k)*sum(b[k-j]/sy.Integer(j)**2 for j in range(1,k+1)))
        assert sy.simplify(un-b[n]/n)==0
        U+=un*q**n
    return {'lambert_chart_residual_through_T2':'exact zero',
            'finite_fold_Y_through_z7':str(expected),
            'finite_fold_H_through_z6':str(Hseries),
            'finite_fold_JY_through_z5':str(Jseries),
            'lagrange_identity_through_degree':N,'rational_U':str(U),
            'v1':str(v1),'v2':str(sy.factor(v2))}


def inverse_diagnostics()->list[dict]:
    out=[]
    c=BC; r0=c/12; r1=-c/288
    for eps in [mp.mpf('1e-4'),mp.mpf('1e-8'),mp.mpf('1e-16')]:
        v=-mp.lambertw(-4*mp.exp(-3)*eps/c,-1)
        T=2*mp.sqrt(eps/(c*v)); e=2/v
        exact=lambda x: x+c*(mp.polylog(3,mp.exp(-x))-D0)-eps
        x=mp.findroot(exact,(T*mp.mpf('.99'),T*mp.mpf('1.01')))
        v1=-2*e*r0/(c*(2-e))
        v2=2*e*(c*r1*(2-e)**2+e*(3*e-10)*r0**2)/(c**2*(e-2)**3)
        x1=T+v1*T*T; x2=x1+v2*T**3
        assert abs(x2-x)<abs(x1-x)<abs(T-x)
        out.append({'epsilon':mp.nstr(eps,10),'T':mp.nstr(T,25),'eta':mp.nstr(e,25),
                    'exact_x':mp.nstr(x,40),'relative_core_error':mp.nstr(abs(T/x-1),12),
                    'relative_first_error':mp.nstr(abs(x1/x-1),12),
                    'relative_second_error':mp.nstr(abs(x2/x-1),12)})
    return out


def finite_folds()->list[dict]:
    out=[]
    beta=float(BC)
    for M in [32,128,512,2048,8192]:
        j=np.arange(1,M+1,dtype=float)
        L=float(mp.harmonic(M))
        eq=lambda y: beta*np.sum(np.exp(j*y/M)/j**2)-1
        y=brentq(eq,0.,1.,xtol=1e-14)
        sigma=y/M
        # Avoid cancellation in the critical-value drift.
        tail0=float(mp.zeta(3,M+1)); tail1=float(mp.zeta(2,M+1))
        rem=np.sum((np.expm1(j*sigma)-j*sigma)/j**3)
        drift=beta*(tail0+sigma*tail1-rem)
        curvature=beta*np.sum(np.exp(j*sigma)/j)
        z=1/L
        Y=z-z**3/2-z**4/12+35*z**5/72+33*z**6/160-1013*z**7/1800
        out.append({'M':M,'L_M':L,'M_L_log_tau':M*L*sigma,
                    'scaled_radius_drift':2*M*M*drift/beta,
                    'predicted_radius_drift':1+1/L-1/(3*L**3),
                    'relative_curvature':curvature/(beta*L),
                    'M_log_tau':y,'Y_7':Y})
    return out


def main()->None:
    parser=argparse.ArgumentParser(); parser.add_argument('--max-n',type=int,default=65536)
    # ProveIt edit (2026-09-29): a run with a smaller --max-n writes into
    # data/max-n-<N>/ instead of shortening the tables article.tex inputs;
    # --output-dir overrides the destination.
    parser.add_argument('--output-dir',type=Path,default=None,
                        help='output directory (default: data/ for --max-n 65536, else data/max-n-<N>/)')
    args=parser.parse_args()
    if args.max_n<256:
        parser.error('--max-n must be at least 256')
    global DATA
    if args.output_dir is not None:
        DATA=args.output_dir.resolve()
    elif args.max_n!=65536:
        DATA=ROOT/'data'/f'max-n-{args.max_n}'
    DATA.mkdir(parents=True,exist_ok=True)
    out={'environment':{'python':platform.python_version(),'numpy':np.__version__,
                        'sympy':sy.__version__,'mpmath':mp.__version__,'scipy':scipy.__version__,
                        'mp_dps':mp.mp.dps},
         'symbolic':symbolic_checks(),'inverse':inverse_diagnostics(),
         'finite_folds':finite_folds(),'coefficients':[],'cutoffs':[],'coupling':[]}
    p0,alias,_=fft_mass(128,float(BC)); pmp=mp_mass(128,BC)
    rel=abs(mp.mpf(p0)/pmp-1)
    assert rel<mp.mpf('1e-10')
    out['fft_check']={'n':128,'relative_error_against_80_digit_recurrence':mp.nstr(rel,12),
                      'exact_arithmetic_alias_bound':alias}
    for n in [256,1024,4096,16384,65536]:
        if n>args.max_n: continue
        a,b,ell=scales(n,BC); p,alias,length=fft_mass(n,float(BC))
        normalized=p*float(b/PHI0)
        out['coefficients'].append({'n':n,'ell':float(ell),'normalized':normalized,
                                  'one_log_order':float(1+G1C/ell),
                                  'two_log_orders':float(1+G1C/ell+G2C/ell**2),
                                  'alias_bound':alias,'fft_length':length})
        for s in [.5,1.,2.]:
            M=max(1,round(s*float(a))); se=M/float(a)
            pm,_,_=fft_mass(n,float(BC),M); ratio=pm/p
            lam=0.; kapp=float(n*BC*mp.zeta(2,M+1)/b)
            v=float(n*BC*mp.harmonic(M)/b**2)
            nu=float(n*BC*mp.zeta(3,M+1))
            pred=math.exp(-nu)*v**-.5*math.exp(-kapp*kapp/(2*v)-float(G1C/ell))
            out['cutoffs'].append({'n':n,'M':M,'s_effective':se,'ratio':ratio,
                                  'leading_profile':math.exp(-1/(2*se*se)),
                                  'refined_profile':pred})
        print('checked coefficient and cutoffs:',n,flush=True)
    n=min(4096,args.max_n)
    for target in [-1.,0.,1.]:
        beta=beta_for_lambda(n,target); a,b,ell=scales(n,beta)
        lam=float(n*(1-beta*D1)/b); gr=g1_ratio(lam)
        p,_,_=fft_mass(n,float(beta))
        phi=float(PHI0*mp.exp(-lam*lam/2))
        M=round(float(a)); pm,_,_=fft_mass(n,float(beta),M)
        kapp=float(n*beta*mp.zeta(2,M+1)/b); v=float(n*beta*mp.harmonic(M)/b**2)
        nu=float(n*beta*mp.zeta(3,M+1))
        pred=math.exp(-nu)*v**-.5*math.exp(lam*lam/2-(lam+kapp)**2/(2*v)-float(gr/ell))
        out['coupling'].append({'n':n,'lambda':lam,'beta':float(beta),
                               'normalized_density':p*float(b)/phi,
                               'first_order_density':float(1+gr/ell),
                               'cutoff_ratio':pm/p,'refined_cutoff':pred})
    out['status']='all exact checks and stated numerical consistency assertions passed'
    # ProveIt edit (2026-09-29): LF line endings on every platform.
    (DATA/'verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
    def table(name,headers,rows,fmt):
        lines=['\\begin{tabular}{'+fmt+'}','\\toprule',' & '.join(headers)+r' \\',r'\midrule']
        lines+=[' & '.join(row)+r' \\' for row in rows]
        lines += [r'\bottomrule',r'\end{tabular}']
        (DATA/name).write_text('\n'.join(lines)+'\n',encoding='utf-8',newline='\n')
    table('coefficient_table.tex',[r'$n$',r'$\ell_n$',r'$b_n p_n/\phi(0)$',r'$1+g_1/\ell_n$',r'$1+g_1/\ell_n+g_2/\ell_n^2$'],
          [[str(r['n']),f"{r['ell']:.4f}",f"{r['normalized']:.8f}",f"{r['one_log_order']:.8f}",f"{r['two_log_orders']:.8f}"] for r in out['coefficients']],'rrrrr')
    table('cutoff_table.tex',[r'$n$',r'$M$',r'$s_n$',r'Actual ratio',r'Leading',r'Refined'],
          [[str(r['n']),str(r['M']),f"{r['s_effective']:.4f}",f"{r['ratio']:.7f}",f"{r['leading_profile']:.7f}",f"{r['refined_profile']:.7f}"] for r in out['cutoffs'] if .9<r['s_effective']<1.1],'rrrrrr')
    table('fold_table.tex',[r'$M$',r'$M L_M\log\tau_M$',r'$2M^2\log(r_M/\rho_c)/c$',r'Three-term prediction'],
          [[str(r['M']),f"{r['M_L_log_tau']:.8f}",f"{r['scaled_radius_drift']:.8f}",f"{r['predicted_radius_drift']:.8f}"] for r in out['finite_folds']],'rrrr')
    table('coupling_table.tex',[r'$\lambda_n$',r'Density ratio',r'First correction',r'Cutoff ratio',r'Refined cutoff'],
          [[f"{r['lambda']:.0f}",f"{r['normalized_density']:.7f}",f"{r['first_order_density']:.7f}",f"{r['cutoff_ratio']:.7f}",f"{r['refined_cutoff']:.7f}"] for r in out['coupling']],'rrrrr')
    print(out['status'])
    print('FFT recurrence check relative error:',out['fft_check']['relative_error_against_80_digit_recurrence'])

if __name__=='__main__':
    main()
