#!/usr/bin/env python3
"""Independent high-precision quadratures of coordinate-subtracted integrands.
Near zero only, finite Taylor series avoid catastrophic cancellation. These
are floating-point diagnostics, not interval certificates. All truncations
and comparison residuals are retained in the JSON record.
"""
import json,sys,time
from pathlib import Path
from math import factorial,comb
from functools import lru_cache
import mpmath as mp
from jets import *
ROOT=Path(__file__).resolve().parents[1]
mp.mp.dps=70
NLOCAL=42
SWITCH=mp.mpf('0.001')
TOL=mp.mpf('1e-43')

def asmp(q): return mp.mpf(q.numerator)/q.denominator if hasattr(q,'numerator') else mp.mpf(q)

def chi(y,lam):
    if y==mp.mpf('.5'): return y
    if y>mp.mpf('.5'): return 1-chi(1-y,lam)
    return mp.atan(lam*mp.tan(mp.pi*y))/mp.pi

def chi_jet(lam,N=NLOCAL):
    # tan(pi*y) is generated from its differential equation.
    t=constant(mp.mpf(0),N)
    for k in range(N):
        t[k+1]=mp.pi*((1 if k==0 else 0)+sum(t[j]*t[k-j] for j in range(k+1)))/(k+1)
    t2=mul(t,t)
    d=scale(mul(add(constant(1,N),t2),inv(add(constant(1,N),scale(t2,lam**2)))),lam)
    return integral(d)

@lru_cache(None)
def gamma_derivative_at_one(m,p):
    if p==0: return mp.stieltjes(m)
    return gamma_derivative_regular(m,p,mp.mpf(1))

def gamma_derivative_regular(m,p,x):
    if m==0: return -mp.polygamma(p,x)
    if p==0: return mp.stieltjes(m,x)
    e=elementary(p)
    return (-1)**(m+p)*mp.factorial(p)*mp.factorial(m)*sum(
        asmp(e[j])*mp.zeta(p+1,x,derivative=m-j)/mp.factorial(m-j)
        for j in range(min(p,m)+1))

def singular_coefficients(m,p,ph):
    r=ph[1:]+[mp.mpf(0)]; L=logarithm(r,mp.log(r[0])); e=elementary(p)
    out=[constant(mp.mpf(0),len(ph)-1) for _ in range(m+1)]
    base=power(r,-p-1)
    for j in range(min(m,p)+1):
        n=m-j; c=(-1)**(p+j)*mp.factorial(p)*mp.factorial(m)*asmp(e[j])/mp.factorial(n)
        for ell in range(n+1): out[ell]=add(out[ell],scale(mul(base,power(L,n-ell)),c*comb(n,ell)))
    return out

def fp_monomial(k,n):
    return mp.mpf(0) if k==1 else -mp.factorial(n)/mp.mpf(k-1)**(n+1)

def direct_circle_fp(m,p,lam):
    ph=chi_jet(lam); sc=singular_coefficients(m,p,ph)
    # Taylor expansion of the regular shifted term, composed with chi.
    reg=[gamma_derivative_at_one(m,p+j)/mp.factorial(j) for j in range(NLOCAL+1)]
    reg=compose(reg,ph)
    head_fp=sum(sc[ell][j]*fp_monomial(p+1-j,ell) for ell in range(m+1) for j in range(p+1))
    def remainder(y):
        if not y: y=mp.mpf('1e-100') # isolated endpoint has no effect on quadrature
        ly=mp.log(y)
        if y<SWITCH:
            out=eval_series(reg,y)
            for ell in range(m+1):
                out+=ly**ell*eval_series(sc[ell][p+1:],y)
            return out
        x=chi(y,lam)
        # Split by the exact Hurwitz shift to keep ordinary Stieltjes evaluations regular.
        e=elementary(p)
        singular=(-1)**p*mp.factorial(p)*sum((-1)**j*mp.factorial(m)*asmp(e[j])*mp.log(x)**(m-j)/mp.factorial(m-j) for j in range(min(m,p)+1))/x**(p+1)
        head=sum(sc[ell][j]*y**(j-p-1)*ly**ell for ell in range(m+1) for j in range(p+1))
        return gamma_derivative_regular(m,p,1+x)+(singular-head)
    ordinary=mp.quad(remainder,[0,SWITCH,mp.mpf('.1'),mp.mpf('.5'),1])
    return ordinary+head_fp,ordinary,head_fp

@lru_cache(None)
def li_jet(order,qtext,m):
    """Independent defining series, |q|<=1/2 in this suite; 800 terms."""
    q=mp.mpf(qtext)
    return mp.fsum(q**n*mp.mpf(n)**(-order)*(-mp.log(n))**m for n in range(1,801))

def spectral_F(p,m,lam):
    q=(1-lam)/(1+lam); qs=mp.nstr(q,mp.mp.dps)
    # Taylor polynomial of Li_{-p-u}; series derivative signs are explicit.
    li=[(-1)**j*li_jet(-p,qs,j)/mp.factorial(j) for j in range(m+2)]
    fac=mp.taylor(lambda u:2*(2*mp.pi)**p*mp.gamma(1-u)*(2*mp.pi)**u*mp.cos(mp.pi*(p+u)/2),0,m+1)
    f=mul(fac,li); e=elementary(p)
    return (-1)**(m+1)*mp.factorial(m)*(f[m+1]-(asmp(e[m+1])*f[0] if m+1<=p else 0))

def circle_contact(m,p,lam):
    ph=chi_jet(lam,max(8,p+2)); r=ph[1:]+[0]; L=logarithm(r,mp.log(lam))
    return (-1)**p*mp.factorial(p)*mul(power(r,-p-1),t_polynomial(m,p,L))[p]

records=[]
def record(name,left,right,**metadata):
    err=abs(left-right); rel=err/max(1,abs(left),abs(right)); ok=rel<TOL
    d={'name':name,'left':mp.nstr(left,62),'right':mp.nstr(right,62),'absolute_residual':mp.nstr(err,8),'scaled_residual':mp.nstr(rel,8),'passed':bool(ok),**metadata}
    records.append(d)
    print(name,mp.nstr(rel,5), 'PASS' if ok else 'FAIL',flush=True)
    if not ok: raise AssertionError(d)

def main():
    start=time.time(); A=mp.euler+mp.log(2*mp.pi)
    for ls in ['0.5','1.5','2','3']:
        lam=mp.mpf(ls); q=(1-lam)/(1+lam)
        # These direct integrands are not evaluated from the spectral formula.
        val=mp.quad(lambda y:mp.loggamma(chi(y,lam)),[0,.25,.5,.75,1])
        record(f'loggamma-ordinary-lambda{ls}',val,mp.log(mp.pi*(lam+1)/lam)/2)
        for m,p in [(0,0),(0,1),(0,2),(0,3),(1,1),(2,1)]:
            fp,ordinary,head=direct_circle_fp(m,p,lam)
            rhs=spectral_F(p,m,lam)-circle_contact(m,p,lam)
            record(f'circle-fp-m{m}-p{p}-lambda{ls}',fp,rhs,ordinary_subtracted_integral=mp.nstr(ordinary,62),analytic_finite_part_head=mp.nstr(head,62))
            if m==0 and p==1:
                record(f'trigamma-ordinary-lambda{ls}',-ordinary,1/lam**2+mp.pi**2*(lam**2-1)/(2*lam**2))
    # Explicit lambda=2 formulas, compared to separately saved quadratures above.
    def lookup(m,p):
        return next(r for r in records if r['name']==f'circle-fp-m{m}-p{p}-lambda2')
    q=-mp.mpf(1)/3; qs=mp.nstr(q,mp.mp.dps)
    r=lookup(0,0)
    record('displayed-digamma-lambda2',-mp.mpf(r['ordinary_subtracted_integral']),-2*li_jet(0,qs,1)-(mp.euler+mp.log(mp.pi))/2)
    r=lookup(1,1)
    record('displayed-stieltjes11-lambda2',mp.mpf(r['ordinary_subtracted_integral']),2*mp.pi**2*li_jet(-1,qs,1)+3*mp.pi**2*A/8-mp.log(2)/4)
    r=lookup(0,2)
    fp_rhs=8*mp.pi**2*li_jet(-2,qs,1)+3*mp.pi**2*(mp.euler+mp.log(4*mp.pi))/4-11*mp.pi**2/8
    record('displayed-polygamma2-lambda2',-mp.mpf(r['ordinary_subtracted_integral']),fp_rhs-mp.mpf(1)/8)
    # Fourier derivative anomaly has an independently computable kernel derivative.
    for p in range(1,7):
        for lam in [mp.mpf('.5'),mp.mpf('2')]:
            q=(1-lam)/(1+lam)
            kernel=lambda x:(1-q*q)/(1-2*q*mp.cos(2*mp.pi*x)+q*q)
            f0=2*(2*mp.pi)**p*mp.cos(mp.pi*p/2)*li_jet(-p,mp.nstr(q,mp.mp.dps),0)
            record(f'poisson-derivative-p{p}-lambda{lam}',mp.diff(kernel,0,p),(-1)**p*f0)
    out={'kind':'high-precision diagnostics, not interval certificates','count':len(records),'passed':all(r['passed'] for r in records),'working_decimal_digits':mp.mp.dps,'scaled_tolerance':str(TOL),'local_series_degree':NLOCAL,'local_series_switch':str(SWITCH),'polylog_series_terms':800,'elapsed_seconds':round(time.time()-start,2),'mpmath':mp.__version__,'python':sys.version,'records':records}
    (ROOT/'data/numerical_checks.json').write_text(json.dumps(out,indent=2))
    print('TOTAL',len(records),'elapsed',time.time()-start,flush=True)
if __name__=='__main__':main()
