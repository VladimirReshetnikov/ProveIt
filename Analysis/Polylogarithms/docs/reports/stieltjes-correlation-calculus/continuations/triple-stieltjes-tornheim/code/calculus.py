"""Numerical utilities for the article; no numerical routine is a proof.

All shifts accepted by the finite-part routines lie strictly inside (0,1).
Working precision is controlled by mpmath.mp.dps in the caller.
"""
from __future__ import annotations
import mpmath as mp


def K(x):
    return mp.pi * mp.cot(mp.pi*x)


def Kprime(x):
    return -mp.pi**2 / mp.sin(mp.pi*x)**2


def I_closed(m: int, d):
    if not isinstance(m,int) or m<0 or not 0<d<1:
        raise ValueError('m must be nonnegative and 0<d<1')
    out=(mp.stieltjes(m+1,1-d)-mp.stieltjes(m+1,d))/(m+1)
    for k in range(1,(m+1)//2+1):
        j=m-2*k+1
        out+=2*mp.factorial(m)*mp.zeta(2*k)/mp.factorial(j)*(
            (1-mp.mpf(2)**(1-2*k))*mp.stieltjes(j,1-d)+mp.stieltjes(j,d))
    if not m%2:
        out-=2*mp.factorial(m)*(2-mp.mpf(2)**(-m-1))*mp.zeta(m+2)
    return out


def rational_stieltjes_difference(p: int,q: int):
    if not (isinstance(p,int) and isinstance(q,int) and 0<p<q):
        raise ValueError('require integers 0<p<q')
    d=mp.mpf(p)/q
    return K(d)*(mp.euler+mp.log(2*mp.pi*q))-2*mp.pi*mp.fsum(
        mp.sin(2*mp.pi*p*r/q)*mp.loggamma(mp.mpf(r)/q) for r in range(1,q))


def cot_coefficients(shifts):
    b=list(shifts)
    if any(not 0<x<1 for x in b) or len(set(b))!=len(b):
        raise ValueError('shifts must be distinct and in (0,1)')
    return [mp.fprod(K(b[j]-b[k]) for k in range(len(b)) if k!=j) for j in range(len(b))]


def direct_stieltjes0_cot_product(shifts):
    """One-sided scale-one finite part at 0, symmetric PV at all cot poles.

    Subtract all singular terms before quadrature. Removable values are
    provided explicitly; no small-cutoff fit or extrapolation is used.
    """
    b=sorted(shifts); A=cot_coefficients(b); n=len(b)
    P0=mp.fprod(K(-t) for t in b)
    P1=mp.fsum(Kprime(-b[j])*mp.fprod(K(-b[k]) for k in range(n) if k!=j) for j in range(n))
    R=[-mp.digamma(b[j])*A[j] for j in range(n)]
    def regular(x):
        if x==0:
            return P1+mp.euler*P0+mp.fsum(R[j]/b[j] for j in range(n))
        for j in range(n):
            if x==b[j]:
                smoothprime=-mp.polygamma(1,x)*A[j]-mp.digamma(x)*mp.fsum(
                    Kprime(x-b[k])*mp.fprod(K(x-b[l]) for l in range(n) if l!=j and l!=k)
                    for k in range(n) if k!=j)
                return smoothprime-P0/x-mp.fsum(R[k]/(x-b[k]) for k in range(n) if k!=j)
        return -mp.digamma(x)*mp.fprod(K(x-t) for t in b)-P0/x-mp.fsum(R[j]/(x-b[j]) for j in range(n))
    return mp.quad(regular,[mp.mpf(0),*b,mp.mpf(1)])+mp.fsum(R[j]*mp.log((1-b[j])/b[j]) for j in range(n))


def direct_loggamma_cot(d):
    if not 0<d<1:raise ValueError('require 0<d<1')
    R=mp.loggamma(d)
    def regular(x):
        if x==d:return mp.digamma(d)
        return mp.loggamma(x)*K(x-d)-R/(x-d)
    return mp.quad(regular,[0,d,1])+R*mp.log((1-d)/d)


def loggamma_cot_closed(d):
    return (mp.diff(lambda s:mp.zeta(s,d),0,2)+mp.diff(lambda s:mp.zeta(s,1-d),0,2))/2+mp.pi**2*(d-mp.mpf('0.5'))/2


def cubic_quarter_integral():
    """PV integral of psi(x) cot(pi(x-1/4)) cot(pi(x-1/2))."""
    b1=mp.mpf(1)/4; b2=mp.mpf(1)/2; p=mp.pi
    r1=-mp.digamma(b1)/p; r2=mp.digamma(b2)/p
    def regular(x):
        if x==0:return -p+r1/b1+r2/b2
        if x==b1:return -mp.polygamma(1,b1)/p-2*mp.digamma(b1)-r2/(b1-b2)
        if x==b2:return mp.polygamma(1,b2)/p-2*mp.digamma(b2)-r1/(b2-b1)
        return mp.digamma(x)*mp.cot(p*(x-b1))*mp.cot(p*(x-b2))-r1/(x-b1)-r2/(x-b2)
    return mp.quad(regular,[0,b1,b2,1])+r1*mp.log(3)


def direct_hurwitz_cot(u,d):
    """Ordinary endpoint integral, PV at d; real u>0, u!=0."""
    if not u>0 or not 0<d<1:raise ValueError('require u>0 and 0<d<1')
    R=mp.zeta(1-u,d)
    def regular(x):
        if x==d:return -(1-u)*mp.zeta(2-u,d)
        return mp.zeta(1-u,x)*K(x-d)-R/(x-d)
    power=max(4,int(mp.ceil(4/u)))
    def left(t):
        if t==0:return mp.mpf(0)
        return regular(d*t**power)*d*power*t**(power-1)
    return mp.quad(left,[0,1])+mp.quad(regular,[d,1])+R*mp.log((1-d)/d)


def T_mellin(r,s,t,z,w):
    """Colored Tornheim Mellin quadrature at nonnegative integral r,s and t>=1.

    Integrate only to R=max(20,(dps+15)*log(10)/2+t). The omitted tail
    is bounded by 4*Gamma(t,2R)/(2**t*Gamma(t)) for unit colors, since
    |Li_j(z*exp(-x))| <= 2*exp(-x) for j>=0 and x>=log(2).
    This avoids enormous-exponent complex-log calls in infinite-range
    quadrature. No arbitrary-order polylog differentiation is performed.
    """
    if any(not isinstance(v,int) for v in (r,s,t)) or min(r,s)<0 or t<1:
        raise ValueError('require integral r,s>=0 and t>=1')
    if abs(z-1)<mp.eps or abs(w-1)<mp.eps or max(abs(z),abs(w))>1+100*mp.eps:
        raise ValueError('require |z|,|w|<=1 and z,w!=1')
    def li(order,arg):
        if order==0:return arg/(1-arg)
        if order==1:return -mp.log(1-arg)
        return mp.polylog(order,arg)
    def integrand(x):
        return x**(t-1)*li(r,z*mp.exp(-x))*li(s,w*mp.exp(-x))
    R=max(mp.mpf(20),(mp.mp.dps+15)*mp.log(10)/2+t)
    return mp.quad(integrand,[0,1,R])/mp.gamma(t)


def six_sector_mellin(orders,shifts):
    """Unnormalized mathcal{T} at positive real integral orders.

    For real orders the negative-frequency sector is the conjugate of
    the positive-frequency sector. Return a real number.
    """
    total=mp.mpf(0)
    for k in range(3):
        i,j=[v for v in range(3) if v!=k]
        z=mp.exp(2j*mp.pi*(shifts[k]-shifts[i]))
        w=mp.exp(2j*mp.pi*(shifts[k]-shifts[j]))
        phase=mp.exp(-.5j*mp.pi*(orders[i]+orders[j]-orders[k]))
        total+=2*mp.re(phase*T_mellin(orders[i],orders[j],orders[k],z,w))
    return total


def direct_triple_gamma0(shifts):
    """Canonical one-sided finite part of three gamma_0 factors.

    Integrate on the three intervals beginning at the singular points.
    Each simple endpoint pole is subtracted in its own unit coordinate.
    """
    b=sorted(mp.frac(a) for a in shifts)
    if len(b)!=3 or len(set(b))!=3:raise ValueError('three distinct circle shifts required')
    total=mp.mpf(0)
    for j,lo in enumerate(b):
        hi=b[j+1] if j+1<len(b) else b[0]+1
        length=hi-lo
        offsets=[mp.frac(lo-a) for a in b]
        others=[l for l in range(3) if l!=j]
        residue=mp.fprod(-mp.digamma(offsets[l]) for l in others)
        smoothprime=mp.fsum(-mp.polygamma(1,offsets[l])*mp.fprod(-mp.digamma(offsets[h]) for h in others if h!=l) for l in others)
        def regular(t):
            if t==0:return mp.euler*residue+smoothprime
            return mp.fprod(-mp.digamma(t+offsets[l]) for l in range(3))-residue/t
        total+=mp.quad(regular,[0,length])+residue*mp.log(length)
    return total


class ZeroOrderPolylogJet:
    """Stable diagnostic evaluation of V_0(z,x) from the article.

    For x<=1 use the convergent Jonquiere expansion, |mu|<=sqrt(1+pi^2)<2*pi.
    For x>1 use the defining logarithmic power series. There is no
    black-box infinitesimal differentiation of polylog. Truncations here
    are floating-point diagnostics, not certified interval evaluations.
    Construct and use this object at the same base mpmath precision.
    """
    def __init__(self):
        self.dps=mp.mp.dps
        self.ell=mp.log(2*mp.pi)
        self.alpha=mp.euler+self.ell+.5j*mp.pi
        N=4*self.dps+20
        self.coeff=[]
        for k in range(N+1):
            if k==0:c=-self.ell/2
            elif k%2==0:
                c=(-1)**(k//2)*mp.zeta(k+1)/(2*(2*mp.pi)**k)
            else:
                c=mp.zeta(-k)/mp.factorial(k)*(self.ell-mp.digamma(k+1)-mp.diff(mp.zeta,k+1)/mp.zeta(k+1))
            self.coeff.append(c)
        self.rev=list(reversed(self.coeff))
        self.drev=list(reversed([k*self.coeff[k] for k in range(1,len(self.coeff))]))
        max_terms=int(mp.ceil((self.dps+35)*mp.log(10)))+30
        self.logs=[mp.mpf(0)]+[mp.log(n) for n in range(1,max_terms+1)]
    def value(self,theta,x):
        q=mp.exp(-x+1j*theta)
        if x<=1:
            mu=-x+1j*theta
            jet=-(mp.euler+mp.log(-mu))/mu+mp.polyval(self.rev,mu)
        else:
            nterms=int(mp.ceil((self.dps+14)*mp.log(10)/x))+8
            power=q;jet=mp.mpc(0)
            for n in range(1,nterms+1):
                jet-=self.logs[n]*power;power*=q
        return jet-self.alpha*q/(1-q)
    def derivative_at_zero(self,theta):
        mu=1j*theta;q=mp.exp(mu)
        jetprime=-(mp.euler+mp.log(-mu)-1)/mu**2-mp.polyval(self.drev,mu)
        return jetprime+self.alpha*q/(1-q)**2


def triple_digamma_mellin(shifts,jet=None):
    """The article's three absolutely convergent integrals for FP of psi^3."""
    if jet is None:jet=ZeroOrderPolylogJet()
    pairs=[]
    for k in range(3):
        indices=[v for v in range(3) if v!=k]
        pair=[]
        for i in indices:
            d=mp.frac(shifts[k]-shifts[i]+mp.mpf('.5'))-mp.mpf('.5')
            if not d:raise ValueError('distinct circle shifts required')
            pair.append(2*mp.pi*d)
        pairs.append(pair)
    F0=mp.fsum(jet.value(a,0)*jet.value(b,0) for a,b in pairs)
    Fprime=mp.fsum(jet.derivative_at_zero(a)*jet.value(b,0)+jet.value(a,0)*jet.derivative_at_zero(b) for a,b in pairs)
    def F(x):return mp.fsum(jet.value(a,x)*jet.value(b,x) for a,b in pairs)
    threshold=mp.mpf(10)**(-mp.mpf(jet.dps)/2)
    def regular(x):
        if x<threshold:return Fprime
        return (F(x)-F0)/x
    R=max(30,(jet.dps+15)*mp.log(10)/2+4)
    moment=mp.quad(regular,[0,1])+mp.quad(lambda x:F(x)/x,[1,3,10,R])
    beta=-jet.ell+.5j*mp.pi
    return -2*mp.re(moment+beta*F0)
