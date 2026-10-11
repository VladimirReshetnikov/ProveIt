"""Quadratic-spectrum identities accompanying the article.

All numerical functions are ordinary arbitrary-precision diagnostics, not
interval certificates. Set mp.mp.dps before calling. No global precision changes
or file writes are made on import. Arguments a and b must be real and positive;
functions using reflected shifts additionally require a < 1.
"""
from __future__ import annotations
import math
from typing import Sequence
import mpmath as mp


def validate(a, b, reflected=True):
    a, b = mp.mpf(a), mp.mpf(b)
    if not (a > 0 and b > 0 and (not reflected or a < 1)):
        raise ValueError('Require b > 0 and 0 < a < 1 (a > 0 for one-sided functions).')
    return a, b


def bell(v: Sequence):
    """All complete exponential Bell polynomials through len(v)."""
    out = [mp.mpf(1)]
    for n in range(1, len(v)+1):
        out.append(mp.fsum(math.comb(n-1,k-1)*v[k-1]*out[n-k]
                           for k in range(1,n+1)))
    return out


def pole_jet(m: int, b):
    if m < 0:
        raise ValueError('Jet order must be nonnegative.')
    v = [2*mp.log(2/b)] + [(-1)**r*mp.factorial(r-1)*(2-2**r)*mp.zeta(r)
                           for r in range(2,m+2)]
    return bell(v)[m+1]/(m+1)


def cutoffs(a, b, digits=None):
    """Conservative truncation choices; not a rigorous error estimator."""
    digits = mp.mp.dps if digits is None else digits
    M = max(0, int(mp.ceil(2*b-min(a,1-a))))
    if min(M+a,M+1-a) < 2*b:
        M += 1
    K = int(mp.ceil((digits*mp.log(10)+25)/(2*mp.log(2))))
    N = int(mp.ceil((digits*mp.log(10)+25)/(2*mp.pi*b)))
    return M, K, N


def counterterm_jet(m, a, b, parity=1, *, M=None, K=None):
    """D_m^+ or D_m^- using exact finite-head + harmonic Hurwitz tail formula."""
    a,b = validate(a,b)
    if parity not in (-1,1) or m < 0:
        raise ValueError('Require parity in {-1,1} and m >= 0.')
    dM,dK,_ = cutoffs(a,b)
    M = dM if M is None else M
    K = dK if K is None else K
    if not b < min(M+a,M+1-a):
        raise ValueError('Tail binomial series requires b < min(M+a,M+1-a).')
    alpha = mp.mpf('0.5') if parity == 1 else mp.mpf(1)
    def one(x):
        Q=x*x+b*b
        pref=1/mp.sqrt(Q) if parity==1 else x/Q
        return pref*(-mp.log(Q))**m-(-2*mp.log(x))**m/x
    head=mp.fsum(one(n+a)+parity*one(n+1-a) for n in range(M))
    h=[mp.mpf(0)]*m
    coeff=mp.mpf(1)
    tail=[]
    for k in range(1,K+1):
        coeff *= -(alpha+k-1)*b*b/k
        for r in range(1,m+1):
            h[r-1] += (alpha+k-1)**(-r)
        B=bell([(-1)**(r-1)*mp.factorial(r-1)*h[r-1] for r in range(1,m+1)])
        tail.append(coeff*mp.fsum(math.comb(m,j)*B[j]*2**(m-j)*
            (mp.zeta(2*k+1,M+a,derivative=m-j)+parity*
             mp.zeta(2*k+1,M+1-a,derivative=m-j)) for j in range(m+1)))
    return head+mp.fsum(tail)


def bessel_jets(max_order, a, b, parity=1, *, N=None):
    """Bessel spectral jets, with order derivatives evaluated independently."""
    a,b=validate(a,b)
    if parity not in (-1,1) or max_order < 0:
        raise ValueError('Require parity in {-1,1} and max_order >= 0.')
    if N is None:
        N=cutoffs(a,b)[2]
    result=[[] for _ in range(max_order+1)]
    alpha=mp.mpf(0) if parity==1 else -mp.mpf('0.5')
    for n in range(1,N+1):
        x=2*mp.pi*b*n
        if parity==1:
            v=[mp.euler+mp.log(4*mp.pi*n/b)]+[
                (-1)**(r+1)*mp.factorial(r-1)*(2**r-1)*mp.zeta(r)
                for r in range(2,max_order+1)]
            ks={r:mp.diff(lambda nu:mp.besselk(nu,x),alpha,r)
                for r in range(0,max_order+1,2)}
            outer=4*mp.cos(2*mp.pi*n*a)
        else:
            v=[mp.euler+mp.log(mp.pi*n/b)]+[
                (-1)**(r+1)*mp.factorial(r-1)*mp.zeta(r)
                for r in range(2,max_order+1)]
            ks={r:mp.diff(lambda nu:mp.besselk(nu,x),alpha,r)
                for r in range(max_order+1)}
            outer=4*mp.pi*mp.sqrt(b*n)*mp.sin(2*mp.pi*n*a)
        B=bell(v)
        for m in range(max_order+1):
            result[m].append(outer*mp.fsum(math.comb(m,r)*B[m-r]*ks[r]
                                           for r in ks if r<=m))
    return [mp.fsum(row) for row in result]


def even_poisson(s,a,b,*,N=None):
    a,b=validate(a,b)
    if N is None:
        N=cutoffs(a,b)[2]
    return (mp.sqrt(mp.pi)*mp.gamma(s-mp.mpf('.5'))*b**(1-2*s)/mp.gamma(s)
        +4*mp.pi**s*b**(mp.mpf('.5')-s)/mp.gamma(s)*mp.fsum(
            n**(s-mp.mpf('.5'))*mp.cos(2*mp.pi*n*a)*
            mp.besselk(s-mp.mpf('.5'),2*mp.pi*b*n) for n in range(1,N+1)))


def one_sided_binomial(s,a,b,*,M=None,K=None):
    a,b=validate(a,b,False)
    M=max(0,int(mp.ceil(2*b-a))) if M is None else M
    K=int(mp.ceil((mp.mp.dps*mp.log(10)+25)/(2*mp.log(2)))) if K is None else K
    if b>=a+M:
        raise ValueError('Tail convergence requires b < a+M.')
    return mp.fsum(((n+a)**2+b*b)**(-s) for n in range(M)) + mp.fsum(
        (-1)**k*mp.rf(s,k)*b**(2*k)/mp.factorial(k)*mp.zeta(2*s+2*k,a+M)
        for k in range(K+1))


def negative_derivative_series(m,a,b,*,M=None,K=None):
    """Z_a'(-m) from differentiated binomial series, not complex Hurwitz formula."""
    a,b=validate(a,b,False)
    if m<0:
        raise ValueError('Require m >= 0.')
    M=max(0,int(mp.ceil(2*b-a))) if M is None else M
    K=max(m+5,int(mp.ceil((mp.mp.dps*mp.log(10)+30)/(2*mp.log(2))))) if K is None else K
    if b>=a+M:
        raise ValueError('Tail convergence requires b < a+M.')
    head=mp.fsum(-((n+a)**2+b*b)**m*mp.log((n+a)**2+b*b) for n in range(M))
    terms=[]
    for k in range(K+1):
        if k<=m:
            p=(-1)**k*mp.factorial(m)/mp.factorial(m-k)
            dp=p*mp.fsum(mp.mpf(1)/(j-m) for j in range(k))
        else:
            p=0
            dp=(-1)**m*mp.factorial(m)*mp.factorial(k-m-1)
        v=dp*mp.zeta(2*k-2*m,a+M)
        if p:
            v+=2*p*mp.zeta(2*k-2*m,a+M,derivative=1)
        terms.append((-1)**k*b**(2*k)/mp.factorial(k)*v)
    return head+mp.fsum(terms)


def negative_hurwitz(m,a,b):
    a,b=validate(a,b,False)
    return 2*mp.re(mp.fsum(math.comb(m,j)*(-2j*b)**(m-j)*
                mp.zeta(-m-j,a+1j*b,derivative=1) for j in range(m+1)))


def negative_polylog(m,a,b):
    a,b=validate(a,b)
    z=mp.exp(-2*mp.pi*b+2j*mp.pi*a)
    local=-2**(2*m+1)*mp.factorial(m)**2*mp.pi*b**(2*m+1)/mp.factorial(2*m+1)
    return local+2*(-1)**m*mp.factorial(m)*mp.fsum(
        mp.factorial(m+j)*b**(m-j)*mp.re(mp.polylog(m+j+1,z))/
        (mp.factorial(j)*mp.factorial(m-j)*4**j*mp.pi**(m+j))
        for j in range(m+1))


def positive_polylog(N,a,b):
    a,b=validate(a,b)
    if N<1:
        raise ValueError('Require N >= 1.')
    z=mp.exp(-2*mp.pi*b+2j*mp.pi*a)
    return (mp.sqrt(mp.pi)*mp.gamma(N-mp.mpf('.5'))/mp.gamma(N)*b**(1-2*N)
        +2*mp.pi**N*b**(-N)/mp.gamma(N)*mp.fsum(
        mp.factorial(N-1+j)*mp.re(mp.polylog(j+1-N,z))/
        (mp.factorial(j)*mp.factorial(N-1-j)*(4*mp.pi*b)**j)
        for j in range(N)))


def positive_polygamma(N,a,b):
    a,b=validate(a,b)
    def xi(r,c):
        return -mp.digamma(c) if r==1 else (-1)**r*mp.polygamma(r-1,c)/mp.factorial(r-1)
    return 2*mp.re(mp.fsum((-1)**(N-r)*math.comb(2*N-r-1,N-r)*
        (-2j*b)**(-(2*N-r))*(xi(r,a+1j*b)+xi(r,1-a+1j*b))
        for r in range(1,N+1)))


def monomial_anomaly(degree,b):
    if degree%2==0:
        return mp.mpf(0)
    k=(degree+1)//2
    return (-1)**k*b**(2*k)/k*(mp.harmonic(2*k)-mp.harmonic(k)/2)


def monomial_quadratic_prime(degree,a,b,*,M=None,K=100):
    """Z_{x^degree}'(0), differentiated local binomial continuation."""
    a,b=validate(a,b,False)
    M=max(0,int(mp.ceil(2*b-a))) if M is None else M
    head=-mp.fsum((n+a)**degree*mp.log((n+a)**2+b*b) for n in range(M))
    terms=[2*mp.zeta(-degree,a+M,derivative=1)]
    for k in range(1,K+1):
        c=(-1)**k*b**(2*k)/k
        if 2*k-degree==1:
            terms.append(c*(mp.stieltjes(0,a+M)+mp.harmonic(k-1)/2))
        else:
            terms.append(c*mp.zeta(2*k-degree,a+M))
    return head+mp.fsum(terms)


def monomial_linear_prime(degree,a,b):
    """Sum F_+'(0)+F_-'(0) using finite polynomial expansion."""
    a,b=validate(a,b,False)
    return 2*mp.re(mp.fsum(math.comb(degree,r)*(-1j*b)**(degree-r)*
        mp.zeta(-r,a+1j*b,derivative=1) for r in range(degree+1)))


def gamma_ratio_bessel(a,b,*,M=None,K=None,N=None):
    a,b=validate(a,b)
    dM,dK,dN=cutoffs(a,b)
    M=dM if M is None else M; K=dK if K is None else K; N=dN if N is None else N
    A=mp.fsum(mp.asinh((n+a)/b)-mp.asinh((n+1-a)/b)-mp.log((n+a)/(n+1-a))
              for n in range(M))
    A+=mp.fsum((-1)**(k+1)*mp.rf(mp.mpf('.5'),k)*b**(2*k)/(2*k*mp.factorial(k))*
        (mp.zeta(2*k,M+a)-mp.zeta(2*k,M+1-a)) for k in range(1,K+1))
    return (2*(a-mp.mpf('.5'))*mp.log(2/b)+2/mp.pi*mp.fsum(
        mp.sin(2*mp.pi*n*a)*mp.besselk(0,2*mp.pi*b*n)/n for n in range(1,N+1))-A)


def multi_quadratic_binomial(s,a,masses,weights,*,K=100):
    """One-sided continued product spectrum with W(x)=sum weights[d]*x**(2*d).

    Independent common-spectral-scale binomial expansion, for diagnostics of
    the several-mass factorization theorem. Avoid spectral pole arguments.
    """
    a=mp.mpf(a);masses=[mp.mpf(t) for t in masses]
    if a<=0 or not masses or min(masses)<=0:
        raise ValueError('Require a>0 and a nonempty list of positive masses.')
    M=max(0,int(mp.ceil(2*max(masses)-a)))
    r=len(masses)
    c=[mp.mpf(1)]+[mp.mpf(0)]*K
    for b in masses:
        qk=[mp.mpf(1)]
        for k in range(1,K+1):qk.append(qk[-1]*(-(s+k-1)*b*b/k))
        c=[mp.fsum(c[j]*qk[k-j] for j in range(k+1)) for k in range(K+1)]
    head=mp.fsum(mp.fsum(w*(n+a)**(2*d) for d,w in enumerate(weights))*
         mp.fprod(((n+a)**2+b*b)**(-s) for b in masses) for n in range(M))
    return head+mp.fsum(w*c[k]*mp.zeta(2*r*s+2*k-2*d,a+M)
               for d,w in enumerate(weights) if w for k in range(K+1))
