#!/usr/bin/env python3
"""Independent finite-part Fourier quadratures and ordinary Gamma integrals.

Singular monomials are integrated by their exponential power series. The
smooth Hurwitz tails are Taylor-expanded about 3/2 and then quadratured.
No contact coefficient is used to construct the integrated left sides.
These are floating-point diagnostics, not interval certificates.
"""
from __future__ import annotations
import json
import math
import platform
from pathlib import Path
from functools import lru_cache
import mpmath as mp

ROOT=Path(__file__).resolve().parents[1]
mp.mp.dps=60
TERMS=120
SING_TERMS=260
TOL=mp.mpf('1e-38')
center=mp.mpf(3)/2
records=[]

def H(n:int,k:int=1): return mp.fsum(mp.mpf(1)/j**k for j in range(1,n+1))

def P(n:int,t):
    return mp.fprod(1+t/j for j in range(1,n+1))

@lru_cache(None)
def zj(s:int,j:int):
    return mp.zeta(s,center) if j==0 else mp.diff(lambda t:mp.zeta(t,center),s,j)

def zseries_gamma(m:int):
    out=[mp.stieltjes(m,center)]
    for j in range(1,TERMS):
        if m==0: c=(-1)**j*zj(j+1,0)
        elif m==1: c=(-1)**(j+1)*(H(j)*zj(j+1,0)+zj(j+1,1))
        elif m==2: c=(-1)**j*((H(j)**2-H(j,2))*zj(j+1,0)+2*H(j)*zj(j+1,1)+zj(j+1,2))
        else: raise ValueError('This independent checker implements m <= 2.')
        out.append(c)
    return out

@lru_cache(None)
def smooth_polygamma(p:int,q:int):
    r=p+q
    if r==0:
        c=zseries_gamma(1)
        out=[(1+(-1)**j)*cj for j,cj in enumerate(c)]
        out[0]-=2*mp.zeta(2)
        return tuple(out)
    out=[]
    for j in range(TERMS):
        z,d=zj(r+j+1,0),zj(r+j+1,1)
        val=mp.factorial(r)*math.comb(r+j,j)*(
            (-1)**(q+j)*((H(p)-H(r+j))*z-d)
            +(-1)**p*((H(q)-H(r+j))*z-d))
        out.append(val)
    return tuple(out)

def integrate_smooth(co,k:int):
    lam=2*mp.pi*1j*k
    return mp.quad(lambda x:mp.polyval(co[::-1],x-mp.mpf('.5'))*mp.exp(-lam*x),[0,mp.mpf('.5'),1])

@lru_cache(None)
def singular(r:int,l:int,k:int):
    lam=2*mp.pi*1j*k
    terms=[]; a=mp.mpc(1)
    for j in range(SING_TERMS):
        if j!=r: terms.append(a*(-1)**l*mp.factorial(l)/mp.mpf(j-r)**(l+1))
        a*=(-lam)/(j+1)
    return mp.fsum(terms)

def kappa00(p:int,q:int):
    r=p+q
    return (-1)**p*(2*mp.zeta(2)+(H(r)-H(p))*(H(r)-H(q))-H(r,2))

def fp_polygamma(p:int,q:int,k:int):
    r=p+q
    sing=mp.factorial(r)*(
        (-1)**q*(singular(r,1,k)+(H(p)-H(r))*singular(r,0,k))
        +(-1)**p*(singular(r,1,-k)+(H(q)-H(r))*singular(r,0,-k)))
    return sing+integrate_smooth(smooth_polygamma(p,q),k)

def bcoef(m:int,p:int,k:int):
    if k==0: return mp.mpf(0)
    L=mp.log(2*mp.pi*abs(k))+mp.sign(k)*1j*mp.pi/2
    logs=[0,mp.euler+L]+[mp.zeta(j)/j for j in range(2,m+2)]
    bs=[mp.mpc(1)]
    for j in range(1,m+2):
        bs.append(mp.fsum(t*logs[t]*bs[j-t] for t in range(1,j+1))/j)
    pc=[mp.mpf(1)]
    for j in range(1,p+1):
        new=pc+[mp.mpf(0)]
        for t,c in enumerate(pc):new[t+1]+=c/j
        pc=new
    return (-1)**m*mp.factorial(m)*((pc[m+1] if m+1<len(pc) else 0)-bs[m+1])

def canonical(m:int,n:int,p:int,q:int,k:int):
    if k==0:return mp.mpf(0)
    return (-1)**p*(2*mp.pi*1j*k)**(p+q)*bcoef(m,p,-k)*bcoef(n,q,k)

def record(name,lhs,rhs,tol=TOL):
    error=abs(lhs-rhs); rel=error/max(1,abs(rhs))
    ok=rel<tol
    records.append({'name':name,'lhs':mp.nstr(lhs,55),'rhs':mp.nstr(rhs,55),
                    'absolute_error':mp.nstr(error,12),'scaled_error':mp.nstr(rel,12),
                    'scaled_tolerance':mp.nstr(tol,8),'passed':bool(ok)})
    if not ok: raise AssertionError(f'{name}: {mp.nstr(error,10)} versus {mp.nstr(tol,10)}')
    print(name, mp.nstr(error,5),flush=True)

pairs=[(0,0),(0,1),(1,0),(0,2),(1,1),(2,0),(1,2),(2,1),(2,2)]
for p,q in pairs:
    r=p+q
    for k in (0,1,2):
        deltafourier=1 if r==0 else (2*mp.pi*1j*k)**r
        record(f'coordinate_fp_mode_p{p}_q{q}_k{k}',fp_polygamma(p,q,k),
               canonical(0,0,p,q,k)-kappa00(p,q)*deltafourier)

# A nontrivial Stieltjes-index pair: J_10 = gamma_2/2 + reflected gamma_2
# + zeta(2)(gamma_0 + reflected gamma_0) - zeta(3).
g0=zseries_gamma(0); g2=zseries_gamma(2)
co=[(mp.mpf('.5')+(-1)**j)*g2[j]+mp.zeta(2)*(1+(-1)**j)*g0[j] for j in range(TERMS)]
co[0]-=mp.zeta(3)
for k in (0,1,2,-1):
    lhs=(mp.mpf('.5')*singular(0,2,k)+singular(0,2,-k)
        +mp.zeta(2)*(singular(0,0,k)+singular(0,0,-k))+integrate_smooth(co,k))
    record(f'coordinate_fp_stieltjes_m1_n0_k{k}',lhs,canonical(1,0,0,0,k)-mp.zeta(3))

# Direct normalized spectral-family quadratures at nonzero u,v, including complex parameters.
def E(u,v): return mp.gamma(1-u)*mp.gamma(1+u+v)/mp.gamma(1+v)
def A(u,v):
    return mp.gamma(1-u)*mp.gamma(1-v)/mp.gamma(1-u-v)*mp.cos(mp.pi*(u-v)/2)/mp.cos(mp.pi*(u+v)/2)

def completed_W_mode(r:int,t,k:int):
    lam=2*mp.pi*1j*k
    co=[]; rf=mp.mpc(1)
    for j in range(TERMS):
        co.append((-1)**j*rf*mp.zeta(1+r+t+j,center))
        rf*= (1+r+t+j)/(j+1)
    smooth=integrate_smooth(co,k)
    a=mp.mpc(1); terms=[]
    for j in range(SING_TERMS):
        if j!=r:terms.append(a/(j-r-t))
        a*=(-lam)/(j+1)
    val=mp.rf(1+t,r)*(mp.fsum(terms)+smooth)
    if r==0 and k==0: val-=1/t
    return val

spectral_cases=[(0,0,mp.mpf('.12'),mp.mpf('-.08'),1),
                (0,2,mp.mpf('.12'),mp.mpf('-.08'),1),
                (1,1,mp.mpf('.12'),mp.mpf('-.08'),-1),
                (2,1,mp.mpc('.08','.03'),mp.mpc('-.06','.02'),1)]
for idx,(p,q,u,v,k) in enumerate(spectral_cases):
    r=p+q;w=u+v;lam=2*mp.pi*1j*k
    lhs=((-1)**q*(P(p,u)*completed_W_mode(r,v,k)-E(u,v)*completed_W_mode(r,w,k))/u
         +(-1)**p*(P(q,v)*completed_W_mode(r,u,-k)-E(v,u)*completed_W_mode(r,w,-k))/v)
    B=A(u,v)*P(r,w)+P(p,u)*P(q,v)-P(p,u)*P(r,v)-P(q,v)*P(r,u)
    kap=(-1)**p*B/(u*v)
    rhs=(-1)**p*lam**r*(mp.gamma(-u)*mp.exp(u*mp.log(-lam))+P(p,u)/u)*(mp.gamma(-v)*mp.exp(v*mp.log(lam))+P(q,v)/v)-kap*lam**r
    record(f'holomorphic_spectral_mode_{idx}',lhs,rhs)

# Ordinary, absolutely convergent log-Gamma correlations.
ell=mp.log(2*mp.pi)
def L(x):return mp.loggamma(x)-ell/2

def covariance_quad(a):
    if not a:return mp.quad(lambda x:L(x)**2,[0,mp.mpf('.5'),1])
    b=1-a
    return (mp.quad(lambda x:L(x)*L(x+a),[0,b/2,b])
            +mp.quad(lambda x:L(x+b)*L(x),[0,a/2,a]))

def phi21(a):
    return mp.zeta(-1,a)+mp.diff(lambda s:mp.zeta(s,a),-1)+mp.diff(lambda s:mp.zeta(s,a),-1,2)/2

def covariance_formula(a):
    if not a:
        return (1+mp.zeta(2))/6-2*mp.diff(mp.zeta,-1)-mp.diff(mp.zeta,-1,2)
    return -phi21(a)-phi21(1-a)+mp.zeta(2)*(a*a-a+mp.mpf(1)/6)
for a in (mp.mpf(0),mp.mpf('.2'),mp.mpf('.37'),mp.mpf('.5')):
    record(f'ordinary_loggamma_covariance_{a}',covariance_quad(a),covariance_formula(a))
# Positive/negative spectral forms of the same ordinary square.
c=mp.euler+ell
positive=(mp.diff(mp.zeta,2,2)-2*c*mp.diff(mp.zeta,2)+(c*c+mp.pi**2/4)*mp.zeta(2))/(2*mp.pi**2)
record('loggamma_positive_negative_zeta_jets',positive,covariance_formula(mp.mpf(0)))

# Deliberately omit the atom: the base test function 1 must reject this.
wrong_error=abs(fp_polygamma(0,0,0))
assert wrong_error>1
out={'status':'all passed','python':platform.python_version(),'mpmath':mp.__version__,
     'working_decimal_precision':mp.mp.dps,'smooth_taylor_terms':TERMS,'singular_exponential_terms':SING_TERMS,
     'diagnostics':len(records),'maximum_absolute_error':mp.nstr(max(mp.mpf(x['absolute_error']) for x in records),12),
     'maximum_scaled_error':mp.nstr(max(mp.mpf(x['scaled_error']) for x in records),12),
     'missing_atom_control_error':mp.nstr(wrong_error,30),'checks':records,
     'evidence_note':'Floating-point comparisons with truncated, convergent Taylor series; not interval certificates.'}
(ROOT/'data'/'numerical_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='checks'},indent=2))
