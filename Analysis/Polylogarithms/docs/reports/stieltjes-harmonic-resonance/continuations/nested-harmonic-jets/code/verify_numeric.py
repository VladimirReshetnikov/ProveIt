#!/usr/bin/env python3
"""Independent high-precision diagnostics; not interval certificates.
Run from any directory. Python 3 and mpmath 1.3.0 are sufficient.
"""
from __future__ import annotations
import json, math, platform, time
from functools import lru_cache
from pathlib import Path
import mpmath as mp

ROOT=Path(__file__).resolve().parents[1]
mp.mp.dps=60
ROWS=[]
TOL=mp.mpf('1e-42')

@lru_cache(None)
def gamma_r(r: int, a):
    return -mp.digamma(a) if r==0 else mp.stieltjes(r,a)

@lru_cache(None)
def zd(k: int, a, r: int):
    return mp.zeta(k,a,derivative=r)

def record(name: str, lhs, rhs, **metadata) -> None:
    err=abs(lhs-rhs); rel=err/max(1,abs(lhs),abs(rhs))
    row={'name':name,'absolute_residual':mp.nstr(err,16),
         'scaled_residual':mp.nstr(rel,16),'lhs':mp.nstr(lhs,30),
         'rhs':mp.nstr(rhs,30),**metadata}
    ROWS.append(row)
    if rel>TOL: raise AssertionError(row)

def product_G(s,z,a,N=16,K=90, omit=None):
    """Finite head and a convergent Hurwitz-zeta expansion of its tail.
    omit drops one linear factor only, used to differentiate at a zero.
    K is a numerical truncation, not a certified error parameter.
    """
    if mp.re(s)<=mp.mpf('.5') or a<=0: raise ValueError('Need Re(s)>1/2 and a>0')
    if abs(z)/(a+N)**mp.re(s)>=mp.mpf('.65'): raise ValueError('Increase N')
    h=-mp.digamma(a) if s==1 else mp.zeta(s,a)-1/(s-1)
    out=mp.exp(z*h)
    for n in range(N):
        t=z/mp.power(n+a,s)
        out*=mp.exp(-t)
        if n!=omit: out*=1+t
    tail=mp.fsum([(-1)**(k-1)*z**k*mp.zeta(k*s,a+N)/k for k in range(2,K+1)])
    return out*mp.exp(tail)

def jet_primitive(r: int, q: int, z,a,N=12,K=85):
    """A_{r,q}: finite polylogarithmic head + accelerated spectral tail."""
    if abs(z)/(a+N)>=mp.mpf('.7'): raise ValueError('Increase N')
    out=(-1)**r*z*gamma_r(r,a)
    for n in range(N):
        x=n+a; logpower=mp.log(x)**r
        out-=(-1)**r*logpower*(mp.polylog(q+1-r,-z/x)+z/x)
    out+=mp.fsum([(-1)**(k-1)*mp.mpf(k)**(r-q-1)*z**k*zd(k,a+N,r)
                 for k in range(2,K+1)])
    return out

def jet_spectral(r,q,z,a,K=120):
    return (-1)**r*z*gamma_r(r,a)+mp.fsum([
        (-1)**(k-1)*mp.mpf(k)**(r-q-1)*z**k*zd(k,a,r)
        for k in range(2,K+1)])

def polygen_jets(s,z,w,R=1,N=320):
    """Unnormalized derivatives d^r/ds^r at fixed depth weight z.
    Propagates the coefficient recurrence; no numerical differentiation.
    """
    b=[mp.mpf(1)]+[mp.mpf(0)]*R
    total=b.copy()
    for n in range(1,N+1):
        if n==1: ratio=[z]+[mp.mpf(0)]*R
        else:
            ln=mp.log(n); lp=mp.log(n-1)
            ratio=[mp.power(n,-s)*(mp.power(n-1,s)*(lp-ln)**r+z*(-ln)**r)
                   for r in range(R+1)]
        b=[mp.fsum([math.comb(r,j)*ratio[j]*b[r-j] for j in range(r+1)])
           for r in range(R+1)]
        wn=w**n
        for r in range(R+1): total[r]+=b[r]*wn
    return total

def resonant_polynomial(s,m,w):
    b=mp.mpf(1); val=b
    for n in range(1,m+1):
        b*=(-mp.power(m,s) if n==1 else mp.power(n,-s)*(mp.power(n-1,s)-mp.power(m,s)))
        val+=b*w**n
    return val

def T_elementary(m,w):
    p=mp.diff(lambda s:resonant_polynomial(s,m,w),1)
    return p-m*mp.log(m)*(1-w)**m*mp.log(1-w)

def raw_depth(s,a,d):
    E=[mp.mpf(1)]
    for j in range(1,d+1):
        E.append(mp.fsum([(-1)**(k-1)*mp.zeta(k*s,a)*E[j-k] for k in range(1,j+1)])/j)
    return E[d]

def finite_part_formula(d,a):
    c=gamma_r(0,a); g1=gamma_r(1,a); z2=zd(2,a,0)
    if d==2:return (c*c-z2)/2-g1
    if d==3:return (c**3-3*c*z2+2*zd(3,a,0))/6-c*g1-zd(2,a,1)+gamma_r(2,a)/4
    if d==4:
        reg=(c**4-6*c*c*z2+3*z2*z2+8*c*zd(3,a,0)-6*zd(4,a,0))/24
        return reg+z2*g1/2-c*zd(2,a,1)-zd(2,a,2)/2+zd(3,a,1)-c*c*g1/2+c*gamma_r(2,a)/4+g1*g1/4-gamma_r(3,a)/36
    raise ValueError('Implemented d=2,3,4')

def run():
    start=time.time(); a=mp.mpf('1.3')
    # Reciprocal Gamma, including complex z and roots beyond the local power disk.
    for aa in [mp.mpf('.5'),mp.mpf(1),a]:
        for z in [mp.mpf('.2'),mp.mpc('.3','.2'),mp.mpf('-2.2')]:
            record('gamma_product',product_G(mp.mpf(1),z,aa),mp.gamma(aa)*mp.rgamma(aa+z),a=str(aa),z=str(z))
    print('Gamma products checked',flush=True)
    # Parameter shifts and the nontrivial multiplication exponential.
    for s in [mp.mpf('.8'),mp.mpf(1),mp.mpc('1.2','.15')]:
        z=mp.mpc('.11','.07')
        record('shift_product',(1+z/a**s)*product_G(s,z,a+1),product_G(s,z,a),s=str(s))
        for q in [2,3]:
            defect=q*mp.log(q) if s==1 else (mp.power(q,s)-q)/(s-1)
            lhs=mp.fprod([product_G(s,z,(a+j)/q) for j in range(q)])
            rhs=mp.exp(z*defect)*product_G(s,mp.power(q,s)*z,a)
            record('multiplication',lhs,rhs,q=q,s=str(s))
    print('Shift and multiplication checked',flush=True)
    # Logarithmic spectral jets and Euler primitives, two different summation directions.
    for aa in [mp.mpf(1),a]:
        for r in range(3):
            for q in [0,1,2]:
                z=mp.mpc('.18','.09')
                record('jet_polylog_vs_spectral',jet_primitive(r,q,z,aa),jet_spectral(r,q,z,aa),a=str(aa),r=r,q=q)
    z=mp.mpc('.17','.08')
    lhs=jet_primitive(1,0,z,a/2)+jet_primitive(1,0,z,(a+1)/2)
    rhs=jet_primitive(1,0,2*z,a)-2*z*mp.log(2)*mp.digamma(a+2*z)+z*mp.log(2)**2
    record('first_jet_distribution',lhs,rhs)
    # Only one zero factor contributes to the first s derivative at a Gamma root.
    for m in range(4):
        x=a+m; z=-x
        lhs=mp.log(x)*product_G(mp.mpf(1),z,a,omit=m)
        rhs=x*mp.log(x)*mp.gamma(a)*(-1)**m*math.factorial(m)
        record('spectral_jet_at_zero',lhs,rhs,m=m,a=str(a))
    print('Spectral jets checked',flush=True)
    # Euler and ordinary primitives. Quadrature does not differentiate polylog order.
    z=mp.mpf('.25'); aa=mp.mpf(1)
    coeff=[(-1)**(k-1)*zd(k,aa,1) for k in range(2,90)]
    def lam1(u):return -u*gamma_r(1,aa)+mp.fsum(c*u**k for k,c in enumerate(coeff,2))
    euler=mp.quad(lambda t:lam1(z*t)/t if t else -z*gamma_r(1,aa),[0,1])
    record('Euler_primitive_quadrature',euler,jet_primitive(1,1,z,aa))
    ordinary=mp.quad(lam1,[0,z])
    N=12;K=85
    primitive=-gamma_r(1,aa)*z*z/2
    primitive+=mp.fsum(mp.log(n+aa)*(z*z/(2*(n+aa))-z+(n+aa)*mp.log1p(z/(n+aa))) for n in range(N))
    primitive+=mp.fsum((-1)**(k-1)*z**(k+1)*zd(k,aa+N,1)/(k+1) for k in range(2,K+1))
    record('ordinary_primitive_quadrature',ordinary,primitive)
    lg=mp.quad(lambda u:mp.loggamma(a)-mp.loggamma(a+u),[0,z])
    rhs=z*mp.loggamma(a)-(mp.zeta(-1,a+z,derivative=1)-mp.zeta(-1,a,derivative=1))+a*z+z*z/2-z/2-z*mp.log(2*mp.pi)/2
    record('loggamma_ordinary_primitive',lg,rhs)
    # Coefficient-propagated all-depth series versus a finite polynomial calculation.
    for w in [mp.mpf('.4'),mp.mpc('-.3','.2'),mp.mpf('.6')]:
        for m in range(1,7):
            jets=polygen_jets(mp.mpf(1),mp.mpf(-m),w,R=1)
            record('polygen_s1',jets[0],(1-w)**m,m=m,w=str(w))
            record('first_polylog_resonance',jets[1],T_elementary(m,w),m=m,w=str(w))
        T2=-2*mp.log(2)*(w*(1-w)+(1-w)**2*mp.log(1-w))
        record('explicit_m2',polygen_jets(mp.mpf(1),mp.mpf(-2),w,R=1)[1],T2,w=str(w))
    for s in [mp.mpf('.7'),mp.mpc('1.2','.1')]:
        for m in range(1,6):
            w=mp.mpc('.35','.1'); z=-mp.power(m,s)
            record('moving_polynomial_truncation',polygen_jets(s,z,w,R=0)[0],resonant_polynomial(s,m,w),s=str(s),m=m)
    print('Polylog resonances checked',flush=True)
    # Independent Cauchy extraction from raw diagonal zeta functions.
    radius=mp.mpf('.035'); M=64
    for aa in [mp.mpf(1),a]:
        for d in [2,3,4]:
            fp=mp.fsum(raw_depth(1+radius*mp.exp(2j*mp.pi*j/M),aa,d) for j in range(M))/M
            record('Cauchy_diagonal_finite_part',fp,finite_part_formula(d,aa),a=str(aa),depth=d,radius=str(radius),nodes=M)
    report={'status':'PASS','precision_decimal_digits':mp.mp.dps,'acceptance_scaled_residual':str(TOL),
            'checks':len(ROWS),'max_absolute_residual':mp.nstr(max(mp.mpf(r['absolute_residual']) for r in ROWS),16),
            'max_scaled_residual':mp.nstr(max(mp.mpf(r['scaled_residual']) for r in ROWS),16),
            'seconds':time.time()-start,'python':platform.python_version(),'mpmath':mp.__version__,
            'status_note':'Arbitrary-precision floating-point diagnostics, not rigorous interval certificates.', 'rows':ROWS}
    (ROOT/'results'/'numeric_verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='rows'},indent=2))

if __name__=='__main__':run()
