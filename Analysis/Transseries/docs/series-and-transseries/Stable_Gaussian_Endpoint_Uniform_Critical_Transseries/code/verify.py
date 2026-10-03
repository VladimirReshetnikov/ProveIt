#!/usr/bin/env python3
"""Reproducible checks for the endpoint-crossover article.

Exact finite algebra is checked with SymPy. Floating-point recurrence and
Fourier quadrature are independent diagnostics, not interval certificates.
No network access is needed. Run from the package root.
"""
from __future__ import annotations
import argparse, csv, json, math, platform
from pathlib import Path
import mpmath as mp
import numpy as np
import scipy
from scipy.integrate import quad
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'data'
mp.mp.dps = 75

def exprel(x):
    return mp.expm1(x) / x if x else mp.mpf(1)

def exact_checks():
    q = sp.Symbol('q')
    tests = []
    # Formal iteration modulo q^8 stabilizes one order per iteration.
    for weights in [[sp.Rational(1,2),sp.Rational(1,3)],
                    [sp.Rational(2,3),sp.Rational(1,5),sp.Rational(1,7)]]:
        nmax=7
        u=sp.S(0)
        for _ in range(nmax):
            new=0
            for j,w in enumerate(weights,1):
                eu=sum((j*u)**k/sp.factorial(k) for k in range(nmax-j+1))
                new += w*q**j*sp.series(eu,q,0,nmax+1-j).removeO()
            u=sp.series(new,q,0,nmax+1).removeO().expand()
        G=sum(w*q**j for j,w in enumerate(weights,1))
        for n in range(1,nmax+1):
            rhs=sp.series(sp.exp(n*G),q,0,n+1).removeO().coeff(q,n)/n
            assert sp.simplify(u.coeff(q,n)-rhs)==0
            tests.append(f'Lagrange identity weights={weights}, n={n}')
    E,F,v,ell,r,L=sp.symbols('E F v ell r L', positive=True)
    gamma=sp.Symbol('gamma')
    J=(2-gamma-sp.log(2))/2
    g0=sp.Rational(3,4)-gamma/2
    full=E*J/2-g0*E-gamma/2-v/2
    claimed=-E*(1-gamma+sp.log(2))/4-(gamma+v)/2
    assert sp.simplify(full-claimed)==0
    tests.append('full Fourier constant')
    trunc=-(E*L+gamma+v)/2-E/(2*ell**2)
    difference=sp.expand(trunc-full)
    claim=E*(-L/2+(1-gamma+sp.log(2))/4-1/(2*ell**2))
    assert sp.simplify(difference-claim)==0
    assert sp.diff(difference,v)==0
    tests.extend(['prefix cancellation','cutoff constant'])
    return tests

def parameters(n: int, theta: float, eta: float=0.0):
    nn=mp.mpf(n)
    eps=mp.mpf(theta)/mp.log(nn)
    alpha=2-eps
    c=1/(mp.zeta(2-eps)+eta)
    def ff(h): return h*exprel(eps*h)
    H=mp.findroot(lambda h: 2*h-mp.log(nn*c)-mp.log(ff(h)),
                  (mp.log(nn)/2,mp.log(nn)/2+mp.log(mp.log(nn))+2))
    F=ff(H); B=mp.exp(H); E=mp.exp(eps*H); r=E/F
    N=(nn*c)**(1/alpha)
    return dict(n=n, theta=theta, eta=eta, eps=eps, alpha=alpha,c=c,
                H=H,F=F,B=B,E=E,r=r,N=N)

def approximations(p, M):
    ell=mp.mpf(M)/p['N']; a=p['alpha']; r=p['r']
    lead=mp.exp(-ell**(-a)/a)
    corr=lead*(1+r/4*(mp.log(2/(r*ell**2))+1-mp.euler-2/ell**2))
    const=p['E']*(1-mp.euler+mp.log(2))/4+(mp.euler+p['eta'])/2
    full_norm=1-const/p['F']
    return float(lead),float(corr),float(full_norm)

def recurrence(p, M):
    n=p['n']; e=np.longdouble(str(p['eps'])); c=np.longdouble(str(p['c']))
    j=np.arange(1,n+1,dtype=np.longdouble)
    weights=c*j**(-3+e)
    weights[0]+=c*np.longdouble(str(p['eta']))
    G1=p['c']*(mp.zeta(3-p['eps'])+p['eta'])
    tail=p['c']*mp.zeta(3-p['eps'],M+1)
    def prob(cut, mass):
        out=np.zeros(n+1,dtype=np.longdouble)
        out[0]=np.exp(np.longdouble(str(-n*mass)))
        if out[0]==0:
            raise ArithmeticError('long-double underflow: use a smaller --max-n')
        jw=j[:cut]*weights[:cut]
        for k in range(1,n+1):
            m=min(k,cut)
            out[k]=(np.longdouble(n)/k)*np.dot(jw[:m],out[k-m:k][::-1])
        return out[n]
    full=prob(n,G1); truncated=prob(M,G1-tail)
    ratio=np.exp(np.longdouble(str(-n*tail)))*truncated/full
    norm=float(full*np.longdouble(str(p['B']*mp.sqrt(2*mp.pi))))
    return float(ratio),norm

def harmonic_moment(s, M):
    """Finite sum j**(-s); direct sum or Euler--Maclaurin at large M.

    The latter is a numerical 14-term evaluation, not an interval enclosure.
    It avoids slow noninteger negative-order Hurwitz-zeta implementations.
    """
    if M <= 128:
        return mp.fsum(mp.mpf(j)**(-s) for j in range(1,M+1))
    if s == 1:
        return mp.digamma(M+1)+mp.euler
    a=mp.mpf(M+1)
    tail=a**(1-s)/(s-1)+a**(-s)/2
    for k in range(1,15):
        tail+=mp.bernoulli(2*k)/mp.factorial(2*k)*mp.rf(s,2*k-1)*a**(-s-2*k+1)
    return mp.zeta(s)-tail

def fourier(p,M):
    """Central Fourier integral, 60 cumulants for the finite cutoff.

    The full polylog expansion uses 16 analytic terms. Integration is stopped
    at |t|=14. Results are checked against the positive recurrence at small n.
    All evaluations here are floating point, not certified enclosures.
    """
    n=p['n']; eps=p['eps']; c=p['c']; B=p['B']; F=p['F']; E=p['E']; eta=p['eta']
    if eps:
        gr=2*mp.gamma(-2+eps)-1/eps
        zr=mp.zeta(1-eps)+1/eps
    else:
        gr=mp.mpf('1.5')-mp.euler; zr=mp.euler
    ee=float(eps); HH=float(p['H']); FF=float(F)
    gr=float(gr); zr=float(zr); ef=float(eta)
    analytic=[complex(n*c*(mp.zeta(3-eps-k)+eta)/B**k/mp.factorial(k))
              for k in range(3,17)]
    def full_integrand(t):
        if t==0: return 1.0
        z=-1j*t
        L=HH-np.log(z)
        fL=np.expm1(ee*L)/ee if ee else L
        kern=fL+gr*np.exp(ee*L)+zr+ef
        exponent=-t*t/(2*FF)*kern
        exponent+=sum(a*(1j*t)**k for k,a in enumerate(analytic,3))
        return float(np.exp(exponent).real)
    d=float(n*c*mp.zeta(2-eps,M+1)/B)
    cumul=[]
    for k in range(2,61):
        moment=harmonic_moment(3-eps-k,M)+eta
        cumul.append(float(n*c*moment/B**k/mp.factorial(k)))
    def cut_integrand(t):
        z=1j*t
        exponent=-1j*t*d+sum(a*z**k for k,a in enumerate(cumul,2))
        return float(np.exp(exponent).real)
    full,errf=quad(full_integrand,0,14,epsabs=2e-12,epsrel=2e-12,limit=250)
    cut,errc=quad(cut_integrand,0,14,epsabs=2e-12,epsrel=2e-12,limit=250)
    survival=float(mp.exp(-n*c*mp.zeta(3-eps,M+1)))
    return survival*cut/full,full*math.sqrt(2/math.pi),max(errf,errc)

def inverse_diagnostic(D, theta, eta=0):
    D=mp.mpf(D); eps=mp.mpf(theta)/D
    c=1/(mp.zeta(2-eps)+eta)
    F=lambda L: L*exprel(eps*L)
    if eps:
        gr=2*mp.gamma(-2+eps)-1/eps; zr=mp.zeta(1-eps)+1/eps
    else:
        gr=mp.mpf('1.5')-mp.euler; zr=mp.euler
    K=lambda L: F(L)+gr*mp.exp(eps*L)+zr+eta
    def delta(L):
        s=mp.exp(-L)
        ans=c*s*s*K(L)/2
        ans+=c*sum((mp.zeta(3-eps-k)+eta)*(-s)**k/mp.factorial(k) for k in range(3,17))
        return ans
    f=F(D/2); E=mp.exp(eps*D/2); a=mp.log(c*f/2)/2
    root=mp.findroot(lambda L: mp.log(delta(L))+D,(D/2+a-1,D/2+a+1))
    s=mp.exp(-root)
    leading=mp.sqrt(2*mp.exp(-D)/(c*f))
    d=(mp.mpf('1.5')-mp.euler)*E+mp.euler+eta
    corrected=leading*(1-(E*a+d)/(2*f))
    return dict(D=float(D),theta=theta,eta=eta,
                leading_rel_error=float(leading/s-1),
                corrected_rel_error=float(corrected/s-1))

def save_csv(name,rows):
    with (DATA/name).open('w',newline='') as f:
        # ProveIt edit (2026-09-29): LF line endings (the csv default is CRLF).
        wr=csv.DictWriter(f,fieldnames=list(rows[0]),lineterminator='\n');wr.writeheader();wr.writerows(rows)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--max-n',type=int,default=4096)
    # ProveIt edit (2026-09-29): a run with --max-n other than the recorded
    # 4096 writes into data/max-n-<N>/ (or --output-dir) instead of replacing
    # the recorded data; the script itself writes run_summary.txt (the text it
    # prints) only after a successful run, so no shell redirection is needed
    # and a failed run cannot truncate the recorded summary.
    ap.add_argument('--output-dir',type=Path,default=None,
                    help='output directory (default: data/ for --max-n 4096, else data/max-n-<N>/)')
    args=ap.parse_args()
    if args.max_n < 512:
        ap.error('--max-n must be at least 512; use 512 for the portable small run')
    global DATA
    if args.output_dir is not None:
        DATA=args.output_dir.resolve()
    elif args.max_n!=4096:
        DATA=ROOT/'data'/f'max-n-{args.max_n}'
    DATA.mkdir(parents=True,exist_ok=True)
    checks=exact_checks()
    rows=[]; discrepancies=[]
    for n in sorted(set([512,min(2048,args.max_n),args.max_n])):
        if n<512: continue
        for theta in [-1.0,0.0,1.0]:
            for eta in [0.0,2.0]:
                p=parameters(n,theta,eta);M=max(1,round(float(p['N'])))
                observed,norm=recurrence(p,M)
                leading,corrected,full_ap=approximations(p,M)
                if n==512:
                    qr,qn,qe=fourier(p,M)
                    discrepancies.extend([abs(qr-observed),abs(qn-norm)])
                rows.append(dict(n=n,theta=theta,eta=eta,M=M,H=float(p['H']),
                                 observed_ratio=observed,leading_ratio=leading,
                                 corrected_ratio=corrected,full_normalized=norm,
                                 full_corrected=full_ap))
    save_csv('recurrence.csv',rows)
    large=[]
    for n in [10**8,10**16,10**32]:
        for theta in [-2.0,0.0,2.0]:
            p=parameters(n,theta);M=int(mp.nint(p['N']))
            obs,norm,err=fourier(p,M);lead,corr,fa=approximations(p,M)
            large.append(dict(n=n,theta=theta,M=M,H=float(p['H']),
                              observed_ratio=obs,leading_ratio=lead,corrected_ratio=corr,
                              full_normalized=norm,full_corrected=fa,quadrature_error_estimate=err))
    save_csv('large_n.csv',large)
    inv=[inverse_diagnostic(D,th) for D in [20,40,80] for th in [-2,0,2]]
    save_csv('inverse.csv',inv)
    report={'exact_checks_passed':len(checks),'exact_checks':checks,
            'max_recurrence_fourier_absolute_difference':max(discrepancies),
            'recurrence_cases':len(rows),'large_n_cases':len(large),'inverse_cases':len(inv),
            'python':platform.python_version(),'numpy':np.__version__,
            'mpmath':mp.__version__,'scipy':scipy.__version__,'sympy':sp.__version__,
            'precision_digits':mp.mp.dps,'numerical_results_are_not_interval_certificates':True}
    (DATA/'verification.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    summary=[json.dumps(report,indent=2),'','Large-n diagnostics:']
    for x in large:
        summary.append(' '.join(str(v) for v in (x['n'],x['theta'],x['observed_ratio'],x['leading_ratio'],x['corrected_ratio'])))
    text='\n'.join(summary)+'\n'
    print(text,end='')
    (DATA/'run_summary.txt').write_text(text,encoding='utf-8',newline='\n')
if __name__=='__main__': main()
