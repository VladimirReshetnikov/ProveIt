"""Reference evaluators for Vertical Lattice Hurwitz Jets.

All reported residuals are floating-point diagnostics, not interval certificates.
The outer lattice and the Lambert series are evaluated by different expansions.
Complex Stieltjes values are obtained from pole-cancelled Euler--Maclaurin jets,
never from mpmath.stieltjes at a nonreal argument.
"""
from __future__ import annotations
import mpmath as mp


def lambert(nu, q, z, derivative=0, terms=120):
    """Order derivative of sum Li_nu(z*q**r), via its Lambert expansion."""
    return mp.fsum(z**k * (-mp.log(k))**derivative /
                   (mp.power(k, nu)*(1-q**k)) for k in range(1, terms+1))


def polylog_order(nu, z, derivative=0, terms=120):
    if derivative == 0:
        return mp.polylog(nu, z)
    return mp.fsum(z**k * (-mp.log(k))**derivative/mp.power(k, nu)
                   for k in range(1, terms+1))


def bracket(s, a, h, M=0, derivative=0, terms=120):
    tau=2*mp.pi/h; q=mp.exp(-tau); z=mp.exp(-tau*a)
    sg=(-1)**derivative
    ans=lambert(1-s,q,z,derivative,terms)
    ans-=polylog_order(1-s,z,derivative,terms)/2
    ans-=polylog_order(2-s,z,derivative,terms)/tau
    for j in range(1,M+1):
        ans-=mp.bernoulli(2*j)*tau**(2*j-1)/mp.factorial(2*j)*polylog_order(2-s-2*j,z,derivative,terms)
    return sg*ans


def remainder(s,w,M=0):
    if s == 1:
        ans=mp.log(w)-mp.digamma(w)-1/(2*w)
    else:
        ans=mp.zeta(s,w)-w**(1-s)/(s-1)-w**(-s)/2
    for j in range(1,M+1):
        ans-=mp.bernoulli(2*j)*mp.rf(s,2*j-1)/mp.factorial(2*j)*w**(1-s-2*j)
    return ans


def em_remainder_at_one(e,w,M=0,shift=50,depth=24):
    """Analytic finite EM approximation to R_M(1+e,w), including e=0."""
    s=1+e; W=w+shift
    if e == 0:
        ratio=mp.log(w)-mp.log(W)
    else:
        ratio=(mp.expm1(-e*mp.log(W))-mp.expm1(-e*mp.log(w)))/e
    ans=mp.fsum((w+k)**(-s) for k in range(shift))+ratio+(W**(-s)-w**(-s))/2
    ans+=mp.fsum(mp.bernoulli(2*j)*mp.rf(s,2*j-1)/mp.factorial(2*j)*W**(1-s-2*j) for j in range(1,depth+1))
    ans-=mp.fsum(mp.bernoulli(2*j)*mp.rf(s,2*j-1)/mp.factorial(2*j)*w**(1-s-2*j) for j in range(1,M+1))
    return ans


def power_tail(p,a,h,N):
    """Sum (a+/-i*h*n)^(-p), n>N, for Re(p)>1."""
    return ((1j*h)**(-p)*mp.zeta(p,N+1+a/(1j*h))+
            (-1j*h)**(-p)*mp.zeta(p,N+1-a/(1j*h)))


def lattice_remainder(s,a,h,M=0,N=20,J=20):
    ans=mp.fsum(remainder(s,a+1j*h*n,M) for n in range(-N,N+1))
    ans+=mp.fsum(mp.bernoulli(2*j)*mp.rf(s,2*j-1)/mp.factorial(2*j)*
                 power_tail(s+2*j-1,a,h,N) for j in range(M+1,J+1))
    return ans


def stieltjes_lattice(m,a,h,N=14,J=18):
    vals=[]
    for n in range(-N,N+1):
        w=a+1j*h*n
        vals.append((-1)**m*mp.diff(lambda e: em_remainder_at_one(e,w),0,m))
    def tail(e):
        s=1+e
        return mp.fsum(mp.bernoulli(2*j)*mp.rf(s,2*j-1)/mp.factorial(2*j)*
                       power_tail(s+2*j-1,a,h,N) for j in range(1,J+1))
    return mp.fsum(vals)+(-1)**m*mp.diff(tail,0,m)


def exponential_jet(j,linear,N=None):
    """Bell coefficient E_j for reciprocal Gamma, optionally at -N."""
    def gen(e):
        ans=linear*e
        for r in range(2,j+1):
            v=(-1)**(r+1)*mp.zeta(r)
            if N is not None:
                v-=mp.fsum(mp.mpf(k)**(-r) for k in range(1,N+1))
            ans+=v*e**r/r
        return mp.exp(ans)
    return mp.diff(gen,0,j)


def stieltjes_rhs(m,a,h):
    tau=2*mp.pi/h; L=mp.log(tau)+mp.euler
    # B_0(1+e)=Q_{-e}; using spectral derivatives of B directly.
    return tau*(-1)**m*mp.fsum(mp.binomial(m,j)*exponential_jet(j,L)*
                              bracket(1,a,h,0,m-j) for j in range(m+1))


def stirling_remainder(w):
    return mp.loggamma(w)-(w-mp.mpf('0.5'))*mp.log(w)+w-mp.log(2*mp.pi)/2


def negative_jet_lattice(N,a,h,cutoff=18,depth=20):
    """Minimal first spectral jet; symmetric prescription for even N."""
    M=(N+1)//2
    # Oversubtract in the even case to avoid a nonabsolute 1/w tail.
    L=M+1 if N%2==0 else M
    ans=mp.fsum(mp.diff(lambda s: remainder(s,a+1j*h*n,L),-N)
                 for n in range(-cutoff,cutoff+1))
    for j in range(L+1,depth+1):
        coeff=(-1)**N*mp.factorial(N)*mp.factorial(2*j-N-2)*mp.bernoulli(2*j)/mp.factorial(2*j)
        ans+=coeff*power_tail(2*j-N-1,a,h,cutoff)
    if N%2==0:
        beta=mp.bernoulli(N+2)/((N+1)*(N+2))
        tau=2*mp.pi/h
        ans+=beta*tau/2*mp.coth(tau*a/2)
    return ans


def negative_jet_rhs(N,a,h):
    tau=2*mp.pi/h; M=(N+1)//2
    ans=(-1)**N*mp.factorial(N)*tau**(-N)*bracket(-N,a,h,M)
    if N%2==0:
        ans+=tau*mp.bernoulli(N+2)/(2*(N+1)*(N+2))
    return ans


def lerch_small(Q,l,A,terms=90):
    return mp.fsum(Q**k/(A+k)**l for k in range(terms))


def D(l,Q,A):
    return (mp.zeta(l,A)-Q*lerch_small(Q,l,A))/(1-Q)


def bilinear_rhs(r,t,a,b,h,modes=60):
    tau=2*mp.pi/h;q=mp.exp(-tau); A=a+b
    ans=tau*mp.gamma(r+t-1)/(mp.gamma(r)*mp.gamma(t))*(mp.zeta(r+t-2,A)-(A-1)*mp.zeta(r+t-1,A))
    for k in range(1,modes+1):
        for R,T,aa in [(r,t,a),(t,r,b)]:
            ans+=tau/(mp.gamma(r)*mp.gamma(t))*q**(aa*k)*mp.fsum(
                mp.binomial(R-1,j)*(tau*k)**(R-1-j)*mp.gamma(j+T)*D(j+T,q**k,A) for j in range(R))
    return ans


def zeta_vertical_coefficients(r,a,orientation,h,degree):
    """Coefficients of zeta(r,a+orientation*i*h/x) as x->0."""
    I=orientation*1j*h
    terms=[(r-1,mp.mpf(1)/(r-1)),(r,mp.mpf('0.5'))]
    terms += [(r+2*j-1,mp.bernoulli(2*j)*mp.rf(r,2*j-1)/mp.factorial(2*j))
              for j in range(1,(degree-r+1)//2+1)]
    out=[mp.mpc(0)]*(degree+1)
    for p,c in terms:
        for k in range(degree-p+1):
            out[p+k]+=c*I**(-p)*(-1)**k*mp.rf(p,k)/mp.factorial(k)*(a/I)**k
    return out


def bilinear_lattice(r,t,a,b,h,N=22,degree=36):
    ans=mp.fsum(mp.zeta(r,a+1j*h*n)*mp.zeta(t,b-1j*h*n) for n in range(-N,N+1))
    for ori in [1,-1]:
        c=zeta_vertical_coefficients(r,a,ori,h,degree)
        d=zeta_vertical_coefficients(t,b,-ori,h,degree)
        for p in range(r+t-2,degree+1):
            coef=mp.fsum(c[j]*d[p-j] for j in range(p+1))
            ans+=coef*mp.zeta(p,N+1)
    return ans


def four_shift_rhs(a,c,b,d,h,modes=60):
    tau=2*mp.pi/h;q=mp.exp(-tau)
    entries=[(a,b,1),(a,d,-1),(c,b,-1),(c,d,1)]
    ans=tau*mp.fsum(sign*(x+y-1)*mp.digamma(x+y) for x,y,sign in entries)
    for k in range(1,modes+1):
        Q=q**k
        ans-=tau/(1-Q)*mp.fsum(sign*(q**(x*k)+q**(y*k))*(mp.digamma(x+y)+Q*lerch_small(Q,1,x+y)) for x,y,sign in entries)
    return ans
