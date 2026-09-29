#!/usr/bin/env python3
"""Reproduce exact identities and floating-point diagnostics for the article.
The exact tests use Fraction and SymPy. Numerical tables are NOT interval certificates.
"""
from __future__ import annotations
import argparse
import csv
import json
import math
from fractions import Fraction as F
from pathlib import Path
import mpmath as mp
import numpy as np
from scipy.integrate import quad
from scipy.special import roots_legendre
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'data'
mp.mp.dps = 75

def exp_coeff(a: list[F], k: int) -> F:
    e = [F(1)] + [F(0)] * k
    for m in range(1, k + 1):
        e[m] = sum((j * a[j] * e[m-j] for j in range(1, m+1)), F(0)) / m
    return e[k]

def direct(w: list[F], N: int) -> list[F]:
    u = [F(0)] * (N+1)
    for n in range(1, N+1):
        u[n] = sum((w[j] * exp_coeff([j*x for x in u], n-j)
                    for j in range(1, n+1)), F(0))
    return u

def lagrange(w: list[F], n: int) -> F:
    return exp_coeff([n*x for x in w], n) / n

def partitions(n: int, largest: int | None = None):
    if n == 0:
        yield ()
        return
    for j in range(min(n, largest or n), 0, -1):
        for tail in partitions(n-j, j):
            yield (j,) + tail

def partition_coefficient(w: list[F], n: int) -> F:
    total = F(0)
    for parts in partitions(n):
        term = F(1, n)
        for j in set(parts):
            k = parts.count(j)
            term *= (n*w[j])**k / math.factorial(k)
        total += term
    return total

def exact_checks():
    records = []
    count = 0
    for beta, M in [(F(1,3), None), (F(2,5), 4)]:
        N = 13
        w = [F(0)] + [beta/F(j**3) if M is None or j <= M else F(0)
                       for j in range(1, N+1)]
        a = direct(w, N)
        for n in range(1, N+1):
            b, c = lagrange(w,n), partition_coefficient(w,n)
            assert a[n] == b == c, (beta,M,n,a[n],b,c)
            count += 2
            records.append({'beta':str(beta),'cutoff':M,'n':n,'coefficient':str(a[n])})
    N=13; w=[F(0)]+[F(1,3*j**3) for j in range(1,N+1)]
    for M in [1,2,4,7,13]:
        wm=[x if j <= M else F(0) for j,x in enumerate(w)]
        for n in range(1,M+1):
            assert lagrange(w,n)==lagrange(wm,n)
            count+=1
    r,a,b,c=sp.symbols('r a b c')
    cs=sp.symbols('c1:5')
    W=1+sum(cs[k-1]*r**k for k in range(1,5))
    eq=sp.series(W**sp.Rational(3,2)+a*r*W**2+b*r**3*W**3-1,r,0,5).removeO()
    sol={}
    for k,ck in enumerate(cs,1):
        sol[ck]=sp.factor(sp.solve(eq.subs(sol).coeff(r,k),ck)[0])
    assert sp.expand(eq.subs(sol)) == 0
    count+=1
    return {'exact_comparisons_passed':count,'coefficients':records,
            'alpha_3_2_hahn_coefficients':{str(k):str(v) for k,v in sol.items()}}

def point_probability_mp(n: int, beta: mp.mpf, alpha: mp.mpf,
                         M: int | None = None) -> np.longdouble:
    """Slower portable fallback when longdouble has insufficient exponent range."""
    cap = n if M is None else min(n, M)
    with mp.workdps(max(mp.mp.dps, 60)):
        total = (mp.zeta(1 + alpha) if M is None else
                 mp.fsum(mp.mpf(j)**(-1-alpha) for j in range(1, M+1)))
        weights = [mp.mpf(j)**(-alpha) for j in range(1, cap+1)]
        p = [mp.exp(-n*beta*total)] + [mp.mpf(0)]*n
        for k in range(1, n+1):
            p[k] = n*beta/k * mp.fsum(
                weights[j-1]*p[k-j] for j in range(1, min(k, cap)+1))
        value = np.longdouble(str(p[n]))
        if p[n] != 0 and value == 0:
            raise ArithmeticError('Final probability is below the output exponent range.')
        return value

def point_probability(n: int, beta: mp.mpf, alpha: mp.mpf,
                      M: int | None = None) -> np.longdouble:
    """P(sum j*N_j=n), independent N_j~Poisson(n*beta/j^(1+alpha))."""
    cap=n if M is None else min(n,M)
    js=np.arange(1,cap+1,dtype=np.longdouble)
    aa=np.longdouble(str(alpha)); bb=np.longdouble(str(beta))
    w=js**(-aa)
    total=mp.zeta(1+alpha) if M is None else mp.fsum(mp.mpf(j)**(-1-alpha) for j in range(1,M+1))
    p=np.zeros(n+1,dtype=np.longdouble)
    p[0]=np.exp(-np.longdouble(n)*bb*np.longdouble(str(total)))
    if p[0]==0:
        return point_probability_mp(n, beta, alpha, M)
    for k in range(1,n+1):
        m=min(k,cap)
        p[k]=n*bb/k*np.dot(w[:m],p[k-m:k][::-1])
    return p[n]

def stable_density(alpha: float, x: float, deriv: int = 0) -> float:
    ca=math.cos(math.pi*alpha/2); sa=math.sin(math.pi*alpha/2)
    def f(t):
        z=complex(ca*t**alpha,-sa*t**alpha-x*t)
        return ((-1j*t)**deriv*np.exp(z)).real
    top=(52/(-ca))**(1/alpha)
    return quad(f,0,top,epsabs=2e-12,epsrel=2e-12,limit=400)[0]/math.pi

def stable_deriv_zero(alpha: mp.mpf, k: int) -> mp.mpf:
    z=(k+1)/alpha
    if abs(z-mp.nint(z)) < mp.mpf('1e-60'):
        return mp.mpf(0)
    return mp.gamma(z)*mp.sin(mp.pi*z)/(mp.pi*alpha)

def truncated_density(alpha: float, L: float, x: float, nodes: int = 800) -> float:
    """Fourier quadrature; cross-check two resolutions. Not a rigorous enclosure."""
    un,uw=roots_legendre(nodes//2)
    tn,tw=roots_legendre(nodes)
    v=(un+1)/2; uw=uw/2
    T=45.0
    t=(tn+1)*T/2; tw=tw*T/2
    power=1/(2-alpha)
    z=t[:,None]*L*v[None,:]**power
    re=-0.5*np.sinc(z/(2*math.pi))**2
    im=np.empty_like(z)
    small=np.abs(z)<0.02
    zs=z[small]
    im[small]=-zs/6+zs**3/120-zs**5/5040+zs**7/362880
    im[~small]=(np.sin(z[~small])-z[~small])/z[~small]**2
    fac=power*L**(2-alpha)/float(mp.gamma(-alpha))
    psi=fac*t*t*((re+1j*im)@uw)
    value=np.dot(tw,np.real(np.exp(psi-1j*x*t)))/math.pi
    return float(value)

def write_csv(name, rows):
    with (OUT/name).open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)

def run(max_n: int):
    OUT.mkdir(exist_ok=True)
    report=exact_checks()
    alpha=mp.mpf(3)/2; beta=1/mp.zeta(alpha); G=mp.gamma(-alpha); B=beta*G
    g0=stable_deriv_zero(alpha,0)
    rows=[]; probs={}
    ns=[n for n in [64,256,1024,4096,8192] if n<=max_n]
    for n in ns:
        bn=(n*B)**(1/alpha)
        pn=point_probability(n,beta,alpha);probs[n]=pn
        normalized=float(np.longdouble(str(bn))*pn)
        c2=n*beta*mp.zeta(alpha-1)/(2*bn**2)
        approx=g0+c2**2/2*stable_deriv_zero(alpha,4)
        rows.append({'n':n,'b_n':float(bn),'normalized_coefficient':normalized,
                     'stable_limit':float(g0),'relative_error':normalized/float(g0)-1,
                     'second_order_approximation':float(approx)})
    write_csv('critical_coefficients.csv',rows)
    crossover=[]
    for n in [v for v in [256,1024,4096] if v<=max_n]:
        for lam in [-1,0,1]:
            # Solve for beta so that n(1-beta*zeta(alpha))/(n*beta*G)^(1/alpha)=lambda.
            f=lambda be: n*(1-be*mp.zeta(alpha))/(n*be*G)**(1/alpha)-lam
            be=mp.findroot(f,(beta*mp.mpf('.9'),beta*mp.mpf('1.1')))
            bn=(n*be*G)**(1/alpha)
            value=float(np.longdouble(str(bn))*point_probability(n,be,alpha))
            pred=stable_density(float(alpha),lam)
            c2=float(n*be*mp.zeta(alpha-1)/(2*bn**2))
            corr=pred+c2*stable_density(float(alpha),lam,2)
            crossover.append({'n':n,'lambda':lam,'beta':float(be),'normalized':value,
                              'limit':pred,'one_correction':corr})
    write_csv('coupling_crossover.csv',crossover)
    profiles=[]
    for L in [0.5,1.0,2.0,4.0]:
        lam=float(mp.mpf(L)**(1-alpha)/((alpha-1)*G))
        den1=truncated_density(float(alpha),L,lam,800)
        den2=truncated_density(float(alpha),L,lam,1600)
        profile=math.exp(-float(1/(alpha*G*mp.mpf(L)**alpha)))*den2/float(g0)
        assert abs(den1-den2)<2e-8
        profiles.append({'L':L,'lambda_L':lam,'density':den2,'profile':profile,
                         'quadrature_difference':abs(den1-den2)})
    write_csv('cutoff_profile.csv',profiles)
    cuts=[]
    for n in [v for v in [256,1024,4096] if v<=max_n]:
        bn=(n*B)**(1/alpha)
        for profile in profiles:
            L=profile['L'];M=max(1,int(mp.floor(L*bn)))
            pn=point_probability(n,beta,alpha,M)
            tail=mp.zeta(1+alpha,M+1)
            ratio=np.exp(-np.longdouble(str(n*beta*tail)))*pn/probs[n]
            cuts.append({'n':n,'L_target':L,'M':M,'M_over_b_n':float(M/bn),
                         'coefficient_ratio':float(ratio),'limiting_profile':profile['profile']})
    write_csv('cutoff_coefficients.csv',cuts)
    def integ1(v):
        return mp.quad(lambda t: 2*mp.expm1(v*t*t)/(t*t) if t else 2*v,[0,1])
    va=mp.findroot(lambda v:integ1(v)-1/(alpha-1),1)
    def integ2(v):
        return mp.quad(lambda t: 2*(mp.expm1(v*t*t)-v*t*t)/t**4 if t else v*v,[0,1])
    D=beta*(va/(alpha-1)-integ2(va)+1/alpha)
    V=beta*mp.quad(lambda t:2*mp.exp(va*t*t),[0,1])
    fold=[]
    for M in [16,64,256,1024]:
        js=[mp.mpf(j) for j in range(1,M+1)]
        h=mp.findroot(lambda hh:beta*mp.fsum(mp.exp(hh*j)/j**alpha for j in js)-1,
                      (va/M,mp.mpf('1.01')*va/M))
        # Stable exact rearrangement avoids subtracting quantities of size one.
        logr=beta*(h*mp.zeta(alpha,M+1)+mp.zeta(1+alpha,M+1)
                    -mp.fsum((mp.expm1(h*j)-h*j)/j**(1+alpha) for j in js))
        variance=beta*mp.fsum(j**(1-alpha)*mp.exp(h*j) for j in js)
        fold.append({'M':M,'M_log_tau':float(M*h),'v_limit':float(va),
                     'scaled_log_radius_gap':float(M**alpha*logr),'D_limit':float(D),
                     'scaled_variance':float(variance/M**(2-alpha)),'V_limit':float(V)})
    write_csv('finite_fold.csv',fold)
    report['constants']={k:mp.nstr(v,60) for k,v in {'alpha':alpha,'beta_c':beta,'B':B,
        'rho_c':mp.exp(-beta*mp.zeta(1+alpha)),'g_alpha_zero':g0,'v_alpha':va,'D_alpha':D,'V_alpha':V}.items()}
    report['numerical_checks']={'largest_n':max(ns),'critical_rows':len(rows),
        'coupling_rows':len(crossover),'cutoff_rows':len(cuts),'profile_rows':len(profiles),
        'max_profile_quadrature_difference':max(p['quadrature_difference'] for p in profiles),
        'arithmetic':'Fraction exact tests; 75-digit constants; numpy.longdouble recurrence; double quadrature',
        'not_interval_certified':True}
    (OUT/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    # Compact generated LaTeX tables.
    def tex_table(filename, spec, header, values):
        text='\\begin{tabular}{'+spec+'}\n\\toprule\n'+header+' \\\\\n\\midrule\n'
        text+='\n'.join(' & '.join(v)+' \\\\' for v in values)
        text+='\n\\bottomrule\n\\end{tabular}\n'
        (OUT/filename).write_text(text)
    tex_table('critical_table.tex','rrrr',r'$n$ & $b_n p_n$ & relative error & corrected value',
              [[str(r['n']),f"{r['normalized_coefficient']:.9f}",f"{r['relative_error']:.3e}",f"{r['second_order_approximation']:.9f}"] for r in rows])
    tex_table('cutoff_table.tex','rrr',r'$L$ & $\mathcal R_{3/2}(L)$ & '+f'$n={max(ns)}$ ratio',
              [[f"{p['L']:.1f}",f"{p['profile']:.8f}",f"{next(c['coefficient_ratio'] for c in cuts if c['n']==max(c['n'] for c in cuts) and c['L_target']==p['L']):.8f}"] for p in profiles])
    tex_table('fold_table.tex','rrr',r'$M$ & $M\log\tau_M$ & $M^{3/2}\log(r_M/\rho_c)$',
              [[str(r['M']),f"{r['M_log_tau']:.9f}",f"{r['scaled_log_radius_gap']:.9f}"] for r in fold])
    print(json.dumps({'passed':report['exact_comparisons_passed'],
                      'constants':report['constants'],'numerics':report['numerical_checks']},indent=2))

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--max-n',type=int,default=4096)
    args=parser.parse_args()
    if args.max_n<256:
        parser.error('--max-n must be at least 256')
    run(args.max_n)
