#!/usr/bin/env python3
"""Independent quadrature/derivative diagnostics (not interval certificates)."""
from __future__ import annotations
import argparse, json, platform, time
from pathlib import Path
import mpmath as mp
import sympy as sp

parser=argparse.ArgumentParser()
parser.add_argument('--dps',type=int,default=65)
args=parser.parse_args()
if args.dps<40: raise ValueError('Use at least 40 decimal digits.')
mp.mp.dps=args.dps
records=[]

def record(name,lhs,rhs,tol='1e-28'):
    err=abs(lhs-rhs)/max(mp.mpf(1),abs(rhs))
    ok=err<mp.mpf(tol)
    records.append({'name':name,'relative_scaled_error':mp.nstr(err,10),'tolerance':tol,'pass':bool(ok)})
    print(name,mp.nstr(err,5),'PASS' if ok else 'FAIL',flush=True)
    if not ok: raise AssertionError(name)

# Taylor subtraction in the original affine variable, not an i*epsilon fit.
def fp_beta(alpha,beta,A,B):
    m=int(mp.nint(alpha+beta)); D=A+B; c=B/D
    f=lambda t: t**(alpha-1)*(1-t)**(beta-1)
    co=mp.taylor(f,c,m+20)
    def rem(t):
        h=t-c
        if abs(h)<mp.mpf('1e-4'):
            return mp.fsum(co[j]*h**(j-m) for j in range(m,len(co)))
        return (f(t)-mp.fsum(co[j]*h**j for j in range(m)))/h**m
    val=mp.quad(rem,[0,c/2,c,(1+c)/2,1])
    for j in range(m):
        p=j-m
        mon=mp.log((1-c)/c) if p==-1 else ((1-c)**(p+1)-(-c)**(p+1))/(p+1)
        val+=co[j]*mon
    return val/(-D)**m

for m,al,A,B in [(1,'.5','.5','.5'),(2,'.7','.8','1.4'),(2,'1.3','1.1','.6'),
                   (3,'1.2','.9','1.7'),(4,'1.6','1.3','.7'),(5,'2.2','.8','1.1')]:
    al,A,B=map(mp.mpf,(al,A,B)); be=m-al
    lhs=mp.gamma(m)/(mp.gamma(al)*mp.gamma(be))*fp_beta(al,be,A,B)
    rhs=mp.cos(mp.pi*al)/(A**al*B**be)
    record(f'beta_finite_part_m{m}_a{al}',lhs,rhs,'1e-26')

# Original t-integrals, with a stable logarithmic ratio at the removable zero.
u=sp.symbols('u')
def centered_moment_quad(r,s,q,A,B):
    m=r+s; D=A+B; c=B/D
    def f(t):
        if not 0<t<1: return mp.mpf(0)
        h=t-c
        if h==0:
            return c**(r-1)*(1-c)**(s-1)*(-D/(A*B))**m if q==m else mp.mpf(0)
        U=mp.log1p(h/c)-mp.log1p(-h/(1-c))
        return t**(r-1)*(1-t)**(s-1)*(U/(-D*h))**m*U**(q-m)
    return mp.quad(f,[0,c/2,c,(1+c)/2,1])

def P_coeff(r,s):
    P=sp.Poly(sp.prod(j+u for j in range(1,r))*sp.prod(j-u for j in range(1,s)),u)
    return [mp.mpf(str(P.nth(j))) for j in range(r+s-1)]

def moment_formula(r,s,q,A,B):
    co=P_coeff(r,s); m=r+s
    terms=[co[q-2*k]*mp.zeta(2*k) for k in range(1,q//2+1) if 0<=q-2*k<len(co)]
    return (-1)**(r+1)*2*mp.factorial(q)/mp.factorial(m-1)*mp.fsum(terms)/A**r/B**s
for r in range(1,4):
    for s in range(1,4):
        for q in range(r+s,r+s+3):
            A,B=mp.mpf('0.8'),mp.mpf('1.3')
            record(f'ordinary_moment_{r}_{s}_{q}',centered_moment_quad(r,s,q,A,B),moment_formula(r,s,q,A,B))

# Classical-polylog primitive, independently checked by ordinary quadrature.
def Rpoly(r,s):
    return sp.expand(u*sp.prod(j+u for j in range(1,r))*sp.prod(j-u for j in range(1,s)))
def polylog_primitive(r,s,z):
    R=Rpoly(r,s); degree=int(sp.degree(R,u)); c=2j*mp.pi
    vals=[sp.lambdify(u,sp.diff(R,u,j),'mpmath') for j in range(degree+1)]
    w=mp.exp(c*z)
    atz=-mp.re(mp.fsum((-1)**j*vals[j](z)*mp.polylog(j+1,w)/c**j for j in range(degree+1)))
    at0=mp.re(mp.fsum((-1)**j*vals[j](0)*mp.zeta(j+1)/c**j for j in range(1,degree+1)))
    return atz+at0
for r in range(1,5):
    for s in range(1,5):
        R=sp.lambdify(u,Rpoly(r,s),'mpmath'); z=mp.mpf('0.37')
        lhs=mp.quad(lambda v:mp.pi*R(v)*mp.cot(mp.pi*v) if v else P_coeff(r,s)[0],[0,z])
        record(f'polylog_primitive_{r}_{s}',lhs,polylog_primitive(r,s,z))
record('polylog_half_endpoint_22',polylog_primitive(2,2,mp.mpf('.5')),
       mp.mpf(3)/8*mp.log(2)+9*mp.zeta(3)/(16*mp.pi**2))

# A fully convergent inverse-logarithm integral; use exp remainder near U=0.
def inverse_log_integral(r,s):
    m=r+s; z=mp.mpf('.5')
    def f(t):
        if not 0<t<1:return mp.mpf(0)
        h=t-mp.mpf('.5')
        if h==0:
            # exp remainder / U ~ z^(m+1) U^m/(m+1)!
            return t**(r-1)*(1-t)**(s-1)*z**(m+1)/mp.factorial(m+1)*(-2)**m
        U=mp.log1p(2*h)-mp.log1p(-2*h)
        if abs(U)<mp.mpf('.1'):
            rem=mp.fsum((z*U)**j/mp.factorial(j) for j in range(m+1,m+55))
        else: rem=mp.exp(z*U)-mp.fsum((z*U)**j/mp.factorial(j) for j in range(m+1))
        return t**(r-1)*(1-t)**(s-1)*rem/(U*(-2*h)**m)
    return mp.quad(f,[0,mp.mpf('.25'),mp.mpf('.5'),mp.mpf('.75'),1])
record('ordinary_inverse_log_11',inverse_log_integral(1,1),(1-mp.log(2))/2)
record('ordinary_inverse_log_22',inverse_log_integral(2,2),
       mp.log(2)/16+3*mp.zeta(3)/(32*mp.pi**2)-mp.mpf(11)/144+mp.pi**2/432)

# Finite Hurwitz reduction of the equal-period Barnes/Mellin kernel.
X=sp.symbols('X')
def ccoeff(m,a):
    co=[mp.mpf(1)]
    for j in range(1,m):
        new=[mp.mpf(0)]*(len(co)+1)
        for k,v in enumerate(co):new[k]+=(j-a)*v;new[k+1]+=v
        co=new
    return co

def Z(m,z,a,deriv=0):
    return mp.fsum(c*mp.zeta(z-k,a,derivative=deriv) for k,c in enumerate(ccoeff(m,a)))/mp.factorial(m-1)
for m in range(1,5):
    for astr in ['.7','1.3','2.2']:
        a=mp.mpf(astr);z=m+mp.mpf('1.4')
        for q in [0,1]:
            lhs=mp.quad(lambda v:v**(z-1)*mp.log(v)**q*mp.exp(-a*v)/(-mp.expm1(-v))**m,[0,1,mp.inf])
            rhs=mp.diff(lambda zz:mp.gamma(zz)*Z(m,zz,a),z,q)
            record(f'mellin_{m}_{astr}_{q}',lhs,rhs)

# Direct Hadamard subtraction at Mellin poles (cutoff in v, scale 1).
def series_g(m,a,N=32):
    base=[mp.mpf(1),mp.mpf('.5')]+[mp.bernoulli(k)/mp.factorial(k) for k in range(2,N)]
    def mul(x,y):return [mp.fsum(x[k]*y[j-k] for k in range(max(0,j-len(y)+1),min(j,len(x)-1)+1)) for j in range(min(N,len(x)+len(y)-1))]
    co=[mp.mpf(1)]
    for _ in range(m):co=mul(co,base)
    return mul(co,[(-a)**k/mp.factorial(k) for k in range(N)])
def pole_quad(m,j,q,a):
    co=series_g(m,a);N=m-j+1
    def reg(v):
        if not v:return mp.mpf(0)
        if v<mp.mpf('.001'):
            return mp.fsum(co[k]*v**(j-m-1+k) for k in range(N,len(co)))*mp.log(v)**q
        raw=v**(j-1)*mp.exp(-a*v)/(-mp.expm1(-v))**m
        sub=mp.fsum(co[k]*v**(j-m-1+k) for k in range(N))
        return (raw-sub)*mp.log(v)**q
    ans=mp.quad(reg,[0,mp.mpf('.001'),mp.mpf('.1'),1])
    ans+=mp.quad(lambda v:v**(j-1)*mp.log(v)**q*mp.exp(-a*v)/(-mp.expm1(-v))**m,[1,mp.inf])
    ans+=mp.fsum(co[k]*(-1)**q*mp.factorial(q)/(j-m+k)**(q+1) for k in range(N-1))
    return ans

def pole_formula(m,j,q,a):
    co=ccoeff(m,a);cj=co[j-1]
    G=[mp.diff(mp.gamma,j,k)/mp.factorial(k) for k in range(q+2)]
    H=[]
    for k in range(q+1):
        term=cj*(-1)**k*mp.stieltjes(k,a)/mp.factorial(k)
        term+=mp.fsum(co[h]*mp.zeta(j-h,a,derivative=k)/mp.factorial(k) for h in range(m) if h!=j-1)
        H.append(term)
    return mp.factorial(q)/mp.factorial(m-1)*(cj*G[q+1]+mp.fsum(G[k]*H[q-k] for k in range(q+1)))
for m,j,astr in [(2,2,'1'),(2,1,'.7'),(3,2,'1.3'),(4,3,'.8')]:
    for q in range(3):
        a=mp.mpf(astr)
        record(f'pole_finite_part_{m}_{j}_{q}_{astr}',pole_quad(m,j,q,a),pole_formula(m,j,q,a),'1e-27')

# Stieltjes--Hurwitz antiderivative: differentiate its closed expression.
for m in [1,2,3]:
    for q in [0,1]:
        a=mp.mpf('1.3');co=ccoeff(m,a)
        lhs=mp.diff(lambda aa:-Z(m,0,aa,deriv=q+1)/mp.factorial(q+1),a)
        rhs=(co[0]*(-1)**q*mp.stieltjes(q,a)+mp.fsum(co[k]*mp.zeta(1-k,a,derivative=q) for k in range(1,m)))/mp.factorial(m-1)/mp.factorial(q)
        record(f'stieltjes_primitive_{m}_{q}',lhs,rhs)

out={'status':'PASS','python':platform.python_version(),'mpmath':mp.__version__,
     'decimal_precision':args.dps,'diagnostic_count':len(records),'records':records,
     'scope':'Floating-point diagnostics, not rigorous enclosures or a proof of the general theorems.'}
Path(__file__).with_name('numeric_results.json').write_text(json.dumps(out,indent=2)+'\n')
print('TOTAL',len(records),'PASS',flush=True)
