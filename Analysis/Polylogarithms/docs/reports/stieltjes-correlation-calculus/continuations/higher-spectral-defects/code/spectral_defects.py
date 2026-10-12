"""Exact coefficient and high-precision evaluation utilities for spectral defects.

All summations below that use a finite `terms` are numerical diagnostics,
not interval-certified evaluations. Polynomial weights are increasing-order lists.
"""
from __future__ import annotations
from functools import lru_cache
from typing import Sequence
import mpmath as mp


def rising_coeffs(k: int, order: int) -> list:
    """Coefficients of (s)_k/k!, through the requested order."""
    if k < 0 or order < 0:
        raise ValueError('k and order must be nonnegative')
    p = [mp.mpf(1)] + [mp.mpf(0)] * order
    for j in range(k):
        p = [(j*p[h] + (p[h-1] if h else 0))/(j+1)
             for h in range(order+1)]
    return p


def D_coeffs(k: int, order: int) -> list:
    if k < 1:
        raise ValueError('k must be positive')
    p, q = rising_coeffs(2*k, order), rising_coeffs(k, order)
    return [2**j*p[j]-q[j] for j in range(order+1)]


def weight(x, w: Sequence):
    return mp.polyval(list(reversed(w)), x)


def zeta_jet(j: int, s, a):
    return mp.zeta(s, a, derivative=j)


def linear_jet(r: int, a, z, w: Sequence):
    """F_W^(r)(0;z), from a finite shifted-Hurwitz expression."""
    return mp.fsum(wd*mp.binomial(d,h)*(-z)**(d-h)*zeta_jet(r,-h,a+z)
                   for d,wd in enumerate(w) if wd for h in range(d+1))


def phi(a, z, w: Sequence):
    if len(w) == 1:
        return w[0]*(mp.loggamma(a+z)-mp.log(2*mp.pi)/2)
    return linear_jet(1,a,z,w)


def finite_head(a, b, factor=2):
    """Choose X=a+N at least factor*b, ensuring a geometric tail."""
    return max(0, int(mp.ceil(factor*abs(b)-a)))


def _pole_product_jet(p: Sequence, r: int, scale, X):
    """Jet of p(s)*zeta(1+scale*s,X), assuming p(0)=0."""
    return mp.factorial(r)*(p[r+1]/scale + mp.fsum(
        p[h]*(-scale)**(r-h)*mp.stieltjes(r-h,X)/mp.factorial(r-h)
        for h in range(1,r+1)))


def quadratic_jet(r: int, a, b, w: Sequence, terms: int=100, head=None):
    """Independent Pochhammer-Hurwitz evaluation of Z_W^(r)(0)."""
    if a <= 0 or b < 0 or r < 0:
        raise ValueError('Require a>0, b>=0, r>=0')
    N = finite_head(a,b) if head is None else int(head)
    X = a+N
    if abs(b) >= X:
        raise ValueError('Tail requires b < a+head')
    values = [weight(a+n,w)*(-mp.log((a+n)**2+b*b))**r for n in range(N)]
    for d,wd in enumerate(w):
        if not wd: continue
        for k in range(terms):
            p = rising_coeffs(k,r+1)
            t = 2*k-d
            if t == 1:
                val = _pole_product_jet(p,r,mp.mpf(2),X)
            else:
                val = mp.factorial(r)*mp.fsum(p[h]*2**(r-h)*
                    zeta_jet(r-h,t,X)/mp.factorial(r-h) for h in range(r+1) if p[h])
            values.append(wd*(-b*b)**k*val)
    return mp.fsum(values)


def defect_jet(r: int, a, b, w: Sequence, terms: int=100, head=None):
    """All-jet defect master, using the double-zero D_k polynomials."""
    if r < 1 or a <= 0 or b <= 0:
        raise ValueError('Require r>=1 and a,b>0')
    N = finite_head(a,b) if head is None else int(head)
    X = a+N
    if b >= X: raise ValueError('Tail requires b < a+head')
    values = []
    for n in range(N):
        x = a+n
        q = 2**(r-1)*((-mp.log(x+1j*b))**r+(-mp.log(x-1j*b))**r)
        q -= (-mp.log(x*x+b*b))**r
        values.append(weight(x,w)*q)
    for d,wd in enumerate(w):
        if not wd: continue
        for k in range(1,terms):
            p = D_coeffs(k,r+1)
            # Enforce exact vanishing, rather than floating-point cancellation.
            p[0]=p[1]=mp.mpf(0)
            t = 2*k-d
            if t == 1:
                val = _pole_product_jet(p,r,mp.mpf(2),X)
            else:
                val = mp.factorial(r)*mp.fsum(p[h]*2**(r-h)*
                    zeta_jet(r-h,t,X)/mp.factorial(r-h) for h in range(2,r+1) if p[h])
            values.append(wd*(-b*b)**k*val)
    return mp.fsum(values)


def odd_harmonic(k: int, p: int=1):
    return mp.fsum(mp.mpf(1)/(2*j+1)**p for j in range(k))


def local_second(w: Sequence,b):
    """Polynomial C_W for Delta_2 = Gamma chord - C_W."""
    return mp.fsum(w[2*k-1]*2*(-1)**k*b**(2*k)/k*
                   (odd_harmonic(k)**2+odd_harmonic(k,2))
                   for k in range(1,len(w)//2+1) if w[2*k-1])


@lru_cache(maxsize=32)
def _gauss_nodes(n: int, dps: int):
    with mp.workdps(dps):
        xs,ws=mp.gauss_quadrature(n,'legendre')
        return tuple(((xs[j]+1)/2,ws[j]/2) for j in range(n))


def integral01(f, nodes: int=64):
    return mp.fsum(w*f(t) for t,w in _gauss_nodes(nodes,mp.mp.dps))


def gamma_chord(a,u,v,w: Sequence=(1,),nodes: int=64):
    """Ordinary removable-endpoint Gamma/Hurwitz polarization integral."""
    if mp.re(a+u)<=0 or mp.re(a+v)<=0:
        raise ValueError('Endpoints must satisfy Re(a+u),Re(a+v)>0')
    if u==v: return mp.mpf(0)
    c=phi(a,u,w)+phi(a,v,w)
    return integral01(lambda t:(c-phi(a,(1-t)*u+t*v,w)-
                         phi(a,t*u+(1-t)*v,w))/(t*(1-t)),nodes)


def conjugate_chord(a,b,w: Sequence=(1,),nodes: int=64):
    """Faster real-coefficient conjugate specialization of gamma_chord."""
    if any(mp.im(c) for c in w):
        return gamma_chord(a,1j*b,-1j*b,w,nodes)
    c=mp.re(phi(a,1j*b,w))
    return 8*integral01(lambda t:(c-mp.re(phi(a,1j*b*t,w)))/(1-t*t),nodes)


def arctan_square(a,b,terms: int=100,head=None):
    N=finite_head(a,b) if head is None else int(head)
    X=a+N
    if b>=X: raise ValueError('Tail requires b<a+head')
    return mp.fsum([mp.atan(b/(a+n))**2 for n in range(N)]+[
        (-1)**(k-1)*odd_harmonic(k)/k*b**(2*k)*mp.zeta(2*k,X)
        for k in range(1,terms)])


def first_bilateral(m: int,a,b):
    """Inherited finite polylogarithmic L_m=E'(-m), including b=0."""
    if m < 0 or not 0<a<1 or b<0: raise ValueError('Invalid L_m parameters')
    if m==0:
        return -mp.log(2*(mp.cosh(2*mp.pi*b)-mp.cos(2*mp.pi*a)))
    z=mp.exp(-2*mp.pi*b+2j*mp.pi*a)
    return -2**(2*m+1)*mp.factorial(m)**2*mp.pi*b**(2*m+1)/mp.factorial(2*m+1)+2*(-1)**m*mp.factorial(m)*mp.fsum(
        mp.factorial(m+j)*b**(m-j)/(mp.factorial(j)*mp.factorial(m-j)*4**j*mp.pi**(m+j))*mp.re(mp.polylog(m+j+1,z)) for j in range(m+1))


def negative_second_bilateral(m: int,a,b,nodes: int=64):
    ep=4*mp.re(mp.fsum(mp.binomial(m,j)*(-2j*b)**(m-j)*zeta_jet(2,-m-j,alpha+1j*b)
                for alpha in (a,1-a) for j in range(m+1)))
    L=first_bilateral(m,a,b)
    integ=integral01(lambda t:(L-mp.fsum(mp.binomial(m,h)*
                  (b*b*(1-t*t))**(m-h)*first_bilateral(h,a,b*t)
                  for h in range(m+1)))/(1-t*t),nodes)
    return ep-4*integ


def covariance(a,b,c,w: Sequence=(1,),nodes: int=64):
    if any(w[d] for d in range(1,len(w),2)):
        raise ValueError('Covariance theorem requires an even polynomial weight')
    if b==c: return mp.mpf(0)
    return mp.fsum(gamma_chord(a,eb*1j*b,ec*1j*c,w,nodes)
                   for eb in (-1,1) for ec in (-1,1)) -conjugate_chord(a,b,w,nodes)-conjugate_chord(a,c,w,nodes)


def quadratic_value(k: int,a,b,w: Sequence=(1,)):
    """Even polynomial W; exact finite reduction at positive integer k."""
    if k<1 or any(w[d] for d in range(1,len(w),2)):
        raise ValueError('Require integer k>=1 and an even weight')
    def base(j):
        if j<=0:
            m=-j
            return mp.fsum(mp.binomial(m,h)*b**(2*(m-h))*mp.zeta(-2*h,a) for h in range(m+1))
        # Derivatives of the polygamma resolvent in the squared mass.
        def R(mu):
            z=mp.sqrt(mu)
            return (mp.digamma(a+1j*z)-mp.digamma(a-1j*z))/(2j*z)
        return (-1)**(j-1)/mp.factorial(j-1)*mp.diff(R,b*b,j-1)
    return mp.fsum(w[d]*mp.binomial(d//2,h)*(-b*b)**(d//2-h)*base(k-h)
                   for d in range(0,len(w),2) if w[d] for h in range(d//2+1))


def hurwitz_primitive(r: int,h: int,a):
    if r<1 or h<0: raise ValueError('Require r>=1,h>=0')
    return mp.factorial(h)/mp.factorial(h+r)*(mp.zeta(-h-r,a,derivative=1)+
         (mp.harmonic(h+r)-mp.harmonic(h))*mp.zeta(-h-r,a))


def beta_moment(a,u,v,w,j: int,p: int):
    """I_(j,p): lower linear jet with a logarithmic beta weight.

    A tanh-sinh quadrature is used for logarithmic endpoint factors.
    Extra working precision protects the removable endpoint subtraction.
    """
    if min(j,p)<0: raise ValueError('Jet and logarithmic orders must be nonnegative')
    if j == 0 and u == -v and mp.re(u) == 0:
        b = mp.im(u)
        def moment(k):
            def f(s):
                P=mp.fprod(1+2*s/(2*q+1) for q in range(k))
                return mp.gamma(1+s)**2/mp.gamma(1+2*s)*(1-1/P)
            return 2*mp.diff(f,0,p+1)/(p+1)
        return mp.fsum(w[2*k-1]*(-1)**k*b**(2*k)/k*moment(k)
                      for k in range(1,len(w)//2+1) if w[2*k-1])
    if p == 0:
        f=(lambda z: phi(a,z,w)) if j==1 else (lambda z: linear_jet(j,a,z,w))
        edge=f(u)+f(v)
        return integral01(lambda t:(edge-f((1-t)*u+t*v)-f(t*u+(1-t)*v))/(t*(1-t)),56)
    target=mp.mp.dps
    with mp.workdps(target+25):
        f=(lambda z: mp.fsum(wd*(-1)**(d+1)*z**(d+1)/(d+1) for d,wd in enumerate(w) if wd)) if j==0 else ((lambda z: phi(a,z,w)) if j==1 else (lambda z: linear_jet(j,a,z,w)))
        fu,fv=f(u),f(v)
        slope=(v-u)*(mp.diff(f,v)-mp.diff(f,u))
        cutoff=mp.power(10,-target-5)
        def integrand(t):
            if t==0 or t==1: return mp.mpf(0)  # quadrature samples interior points
            z=min(t,1-t)
            ratio=slope if z<cutoff else (fu+fv-f((1-t)*u+t*v)-f(t*u+(1-t)*v))/(t*(1-t))
            return ratio*mp.log(t*(1-t))**p
        ans=mp.quad(integrand,[0,mp.mpf('.5'),1])
    return +ans


def beta_defect(r: int,a,b,w: Sequence):
    """Finite lower-jet beta formula; intended for small r diagnostic checks."""
    if r<1: raise ValueError('r must be positive')
    beta=mp.taylor(lambda s:mp.gamma(1+2*s)/mp.gamma(1+s)**2,0,r-1)
    total=mp.mpc(0)
    even=not any(w[d] for d in range(1,len(w),2))
    for m in range(r):
        if m==1: continue   # beta_1=0 exactly
        for j in range(r-m):
            p=r-1-m-j
            if j==0 and even: continue
            total+=beta[m]*2**j/mp.factorial(j)/mp.factorial(p)*beta_moment(a,1j*b,-1j*b,w,j,p)
    return mp.factorial(r)/4*total


def first_weighted_quadratic(a,b,w: Sequence):
    """Even-weight first jet, evaluated without an anomaly."""
    if any(w[d] for d in range(1,len(w),2)):
        raise ValueError('Require even W')
    return linear_jet(1,a,1j*b,w)+linear_jet(1,a,-1j*b,w)


def mass_chord(a,b,c,w: Sequence=(1,),nodes: int=64,bilateral=False):
    """Second-jet covariance as a squared-mass chord of FIRST jets."""
    if b==c: return mp.mpf(0)
    mu,nu=b*b,c*c
    def T(x):
        y=mp.sqrt(x)
        if bilateral:
            return mp.fsum(w[d]*mp.binomial(d//2,h)*(-x)**(d//2-h)*first_bilateral(h,a,y)
                       for d in range(0,len(w),2) if w[d] for h in range(d//2+1))
        return first_weighted_quadratic(a,y,w)
    edge=T(mu)+T(nu)
    return integral01(lambda t:(edge-T((1-t)*mu+t*nu)-T(t*mu+(1-t)*nu))/(t*(1-t)),nodes)


def two_mass_jet(r: int,a,b,c,w: Sequence=(1,),terms: int=100,head=None):
    """Independent double-binomial expansion about the common mass b.

    Uses a global finite head, then an expansion of
    (x^2+b^2)^(-s)(x^2+c^2)^(-s) in inverse powers of x^2.
    This test utility is restricted to even W, so no pole lies at s=0.
    """
    if any(w[d] for d in range(1,len(w),2)): raise ValueError('Require even W')
    N=finite_head(a,max(b,c)) if head is None else int(head)
    X=a+N
    if max(b,c)>=X: raise ValueError('Tail requires max(b,c)<a+head')
    out=[weight(a+n,w)*(-mp.log(((a+n)**2+b*b)*((a+n)**2+c*c)))**r for n in range(N)]
    ps=[rising_coeffs(k,r) for k in range(terms)]
    for k in range(terms):
        coeff=[mp.mpf(0)]*(r+1)
        for i in range(k+1):
            fac=(-b*b)**i*(-c*c)**(k-i)
            for h in range(r+1):
                coeff[h]+=fac*mp.fsum(ps[i][ell]*ps[k-i][h-ell] for ell in range(h+1))
        for d,wd in enumerate(w):
            if not wd: continue
            out.append(wd*mp.factorial(r)*mp.fsum(coeff[h]*4**(r-h)*
               zeta_jet(r-h,2*k-d,X)/mp.factorial(r-h) for h in range(r+1) if coeff[h]))
    return mp.fsum(out)
