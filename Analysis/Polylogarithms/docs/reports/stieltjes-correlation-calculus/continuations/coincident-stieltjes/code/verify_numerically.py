#!/usr/bin/env python3
"""Independent local-series integration and numerical identity diagnostics.

The local integral evaluator does not use the gamma-quotient moment formula.
It integrates a convergent Laurent-log expansion on (0,b) and uses quadrature
on [b,1]. These are high-precision diagnostics, not interval certificates.
"""
from __future__ import annotations
import argparse, json, math, sys, time
from functools import lru_cache
from pathlib import Path
import mpmath as mp
import sympy as sp
from exact_engine import Engine, L, pc, u, zsym, gsym

@lru_cache(None)
def zder(k:int,j:int):
    return mp.zeta(k,derivative=j)

@lru_cache(None)
def numeric_pc(k:int,j:int):
    """Low coefficient of prod(1+u/h), without expanding a degree-k polynomial."""
    if j<0 or j>k:return mp.mpf('0')
    if j==0:return mp.mpf('1')
    return numeric_pc(k-1,j)+numeric_pc(k-1,j-1)/k

@lru_cache(None)
def gdcoef(m:int,k:int,a:int=1):
    """gamma_m^(k)(a)/k!; a=1 or 2, m,k nonnegative."""
    if k==0:
        return mp.stieltjes(m)-(1 if a==2 and m==0 else 0)
    val=mp.mpf('0')
    for j in range(m+1):
        p=numeric_pc(k,m-j)
        if p:
            zz=zder(k+1,j)-(1 if a==2 and j==0 else 0)
            val+=p*zz/mp.factorial(j)
    return (-1)**(m+k)*mp.factorial(m)*val

@lru_cache(None)
def singular_poly(m:int,p:int):
    ll=sp.Symbol('ll');t=ll**m
    for j in range(p):t=sp.diff(t,ll)-(j+1)*t
    pol=sp.Poly(sp.expand(t),ll)
    return tuple(mp.mpf(int(pol.nth(j))) for j in range(max(0,pol.degree())+1))

def peval(coeff,x):
    ans=mp.mpf('0')
    for c in reversed(coeff):ans=ans*x+c
    return ans

@lru_cache(None)
def smooth_coeffs(m:int,p:int,a:int,M:int):
    return tuple(gdcoef(m,p+j,a)*mp.factorial(p+j)/mp.factorial(j) for j in range(M+1))

def value(m:int,p:int,x,M:int):
    if m==0:return -mp.polygamma(p,x)
    # Split the singular term and evaluate the smooth function about 1 or 2.
    a=1 if x<=mp.mpf('.5') else 2
    y=x if a==1 else x-1
    sm=peval(smooth_coeffs(m,p,a,M),y)
    return x**(-p-1)*peval(singular_poly(m,p),mp.log(x))+sm

def int_monomial(e:int,k:int,b):
    ll=mp.log(b)
    if e==-1:return ll**(k+1)/(k+1)
    a=e+1
    return b**a*mp.fsum((-1)**j*mp.factorial(k)/mp.factorial(k-j)*ll**(k-j)/mp.mpf(a)**(j+1) for j in range(k+1))

def local_integral(p:int,q:int,m:int,n:int,b,M:int):
    """Finite part of the local power-log product, with truncated analytic tails."""
    tp=singular_poly(m,p);tq=singular_poly(n,q)
    ap=smooth_coeffs(m,p,1,M);aq=smooth_coeffs(n,q,1,M)
    terms=[]
    for j,x in enumerate(tp):
        for k,y in enumerate(tq):
            if x and y:terms.append(x*y*int_monomial(-p-q-2,j+k,b))
    for j,x in enumerate(tp):
        if x:
            for k,y in enumerate(aq):terms.append(x*y*int_monomial(k-p-1,j,b))
    for j,x in enumerate(tq):
        if x:
            for k,y in enumerate(ap):terms.append(x*y*int_monomial(k-q-1,j,b))
    # Analytic product: convolution, then elementary integration.
    for k in range(2*M+1):
        c=mp.fsum(ap[j]*aq[k-j] for j in range(max(0,k-M),min(M,k)+1))
        terms.append(c*b**(k+1)/(k+1))
    return mp.fsum(terms)

def direct_moment(p:int,q:int,m:int,n:int,b,M:int,tail_M:int):
    head=local_integral(p,q,m,n,b,M)
    tail=mp.quad(lambda x:value(m,p,x,tail_M)*value(n,q,x,tail_M),[b,mp.mpf('.25'),mp.mpf('.5'),1])
    return head+tail

def eval_expr(expr):
    ss={}
    for sym in expr.free_symbols:
        name=str(sym)
        if name.startswith('g_'):
            z=mp.stieltjes(int(name.split('_')[1]))
        elif name.startswith('zd_'):
            _,r,j=name.split('_');z=zder(int(r)+1,int(j))
        else:raise ValueError(f'unknown numeric symbol: {name}')
        ss[sym]=sp.Float(str(z),mp.mp.dps)
    return mp.mpf(str(expr.subs(ss).evalf(mp.mp.dps)))

def K(s,t):
    return 2*mp.gamma(1-s)*mp.gamma(1-t)*(2*mp.pi)**(s+t-2)*mp.cos(mp.pi*(s-t)/2)*mp.zeta(2-s-t)

def E(a,b):return mp.gamma(1-a)*mp.gamma(1+a+b)/mp.gamma(1+b)

def A(a,b):
    return mp.gamma(1-a)*mp.gamma(1-b)/mp.gamma(1-a-b)*mp.cos(mp.pi*(a-b)/2)/mp.cos(mp.pi*(a+b)/2)

def W(r,t,x=1):return mp.rf(1+t,r)*mp.zeta(1+r+t,x)

def H(r,p,q,a,b):
    pp=lambda k,t:mp.rf(1+t,k)/mp.factorial(k)
    return (-1)**q*(pp(p,a)*W(r,b)-E(a,b)*W(r,a+b))/a+(-1)**p*(pp(q,b)*W(r,a)-E(b,a)*W(r,a+b))/b

def cp(p,a):return (-1)**p*mp.rf(1+a,p)

def J00(p,q,a):
    r=p+q;b=1-a
    if r==0:return mp.stieltjes(1,a)+mp.stieltjes(1,b)-2*mp.zeta(2)
    return mp.factorial(r)*(
        (-1)**q*((mp.harmonic(p)-mp.harmonic(r))*mp.zeta(r+1,a)-mp.zeta(r+1,a,derivative=1))
       +(-1)**p*((mp.harmonic(q)-mp.harmonic(r))*mp.zeta(r+1,b)-mp.zeta(r+1,b,derivative=1)))

def Jregular00(p,q,a):
    r=p+q
    if r==0:return mp.stieltjes(1,1+a)+mp.stieltjes(1,1-a)-2*mp.zeta(2)
    return mp.factorial(r)*(
        (-1)**q*((mp.harmonic(p)-mp.harmonic(r))*mp.zeta(r+1,1+a)-mp.zeta(r+1,1+a,derivative=1))
       +(-1)**p*((mp.harmonic(q)-mp.harmonic(r))*mp.zeta(r+1,1-a)-mp.zeta(r+1,1-a,derivative=1)))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--dps',type=int,default=55)
    ap.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'data'/'numerical_validation.json');args=ap.parse_args()
    if args.dps<40:raise ValueError('use at least 40 decimal digits')
    mp.mp.dps=args.dps;eng=Engine(6);rows=[];start=time.time()
    def check(name,lhs,rhs,tol):
        err=abs(lhs-rhs);passed=err<=tol*(1+abs(rhs))
        row=dict(name=name,lhs=mp.nstr(lhs,45),rhs=mp.nstr(rhs,45),abs_error=mp.nstr(err,8),relative_tolerance=mp.nstr(tol,5),passed=bool(passed));rows.append(row)
        print(name,'PASS' if passed else 'FAIL',mp.nstr(err,6),flush=True)
        if not passed:raise AssertionError(row)
    # The classical convergent product formula is checked without continuation.
    for s,t in [('-.3','-.7'),('.2','-.4'),('.15','.25')]:
        s=mp.mpf(s);t=mp.mpf(t)
        lhs=mp.quad(lambda x:mp.zeta(s,x)*mp.zeta(t,x),[0,mp.mpf('.125'),mp.mpf('.5'),1])
        check(f'classical_K_{s}_{t}',lhs,K(s,t),mp.mpf('1e-28'))
    # Independent coincident finite-part moments.
    cases=[(p,r-p,0,0) for r in range(5) for p in range(r+1)]
    cases +=[(0,0,1,0),(0,0,1,1),(0,0,2,0),(0,0,2,1),
             (0,1,1,0),(1,0,1,0),(1,1,1,0),(0,2,1,1),(1,0,2,0)]
    b=mp.mpf('.125');local_M=52;tail_M=145
    for p,q,m,n in cases:
        got=direct_moment(p,q,m,n,b,local_M,tail_M)
        want=eval_expr(eng.moment(p,q,m,n))
        check(f'local_quadrature_p{p}_q{q}_m{m}_n{n}',got,want,mp.mpf('2e-30'))
    # Change the splitting point as an independent numerical stability check.
    for case in [(0,0,1,1),(1,1,0,0),(0,2,1,1)]:
        p,q,m,n=case;b2=mp.mpf('0.1')
        got=direct_moment(p,q,m,n,b2,56,tail_M)
        check(f'split_point_{case}',got,eval_expr(eng.moment(p,q,m,n)),mp.mpf('2e-30'))
    # Off-origin gamma identities: direct Fourier kernel versus regular completion.
    aa=mp.mpf('.037');bb=mp.mpf('-.061')
    base=(aa*mp.zeta(1+aa)+bb*mp.zeta(1+bb)-1-A(aa,bb)*(aa+bb)*mp.zeta(1+aa+bb))/(aa*bb)
    comp=K(1+aa,1+bb)+mp.zeta(1+aa)/bb+mp.zeta(1+bb)/aa-1/(aa*bb)
    check('base_holomorphic_completion',base,comp,mp.mpf('1e-45'))
    for p,q in [(0,1),(1,1),(0,3),(2,2),(1,4)]:
        r=p+q
        raw=cp(p,aa)*cp(q,bb)*K(1+p+aa,1+q+bb)
        completed=raw+cp(p,aa)*cp(r,bb)*mp.zeta(1+r+bb)/(mp.factorial(p)*aa)+cp(q,bb)*cp(r,aa)*mp.zeta(1+r+aa)/(mp.factorial(q)*bb)
        check(f'derivative_completion_{p}_{q}',H(r,p,q,aa,bb),completed,mp.mpf('1e-44'))
    # Exact shifted singular decomposition, at two shifts for each derivative pair.
    for p,q in [(0,0),(0,1),(1,0),(1,1),(0,3),(2,2)]:
        r=p+q
        for astr in ['.07','.31']:
            a=mp.mpf(astr)
            singular=(-1)**q*mp.factorial(r)*a**(-r-1)*(mp.log(a)+mp.harmonic(p)-mp.harmonic(r))
            check(f'shifted_split_{p}_{q}_{astr}',J00(p,q,a)-singular,Jregular00(p,q,a),mp.mpf('1e-40'))
    # Log-Gamma primitive moment (ordinary convergent integral).
    kappa=mp.euler+mp.log(2*mp.pi)
    rhs=(mp.zeta(2,derivative=2)-2*kappa*mp.zeta(2,derivative=1)+(kappa*kappa+mp.pi**2/4)*mp.zeta(2))/(2*mp.pi**2)
    got=mp.quad(lambda x:(mp.loggamma(x)-mp.log(2*mp.pi)/2)**2,[0,mp.mpf('.125'),mp.mpf('.5'),1])
    check('ordinary_loggamma_square',got,rhs,mp.mpf('1e-45'))
    result=dict(status='passed',count=len(rows),dps=args.dps,local_terms=local_M,tail_terms=tail_M,
                method='Laurent-log local integration plus ordinary quadrature; no interval enclosures',
                python=sys.version,mpmath=mp.__version__,elapsed_seconds=round(time.time()-start,3),checks=rows)
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(result,indent=2)+'\n')
    print('TOTAL',len(rows),'checks; elapsed',result['elapsed_seconds'],'seconds')

if __name__=='__main__':main()
