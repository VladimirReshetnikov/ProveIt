"""Formula and quadrature helpers for vertical-line Hurwitz pairings.

All singular spectral values of finite formulas must be evaluated by the
specified removable limits, never by evaluating singular summands separately.
These are floating-point diagnostics, not interval certificates.
"""
from __future__ import annotations
from functools import lru_cache
import mpmath as mp


def valuation(depth: int) -> int:
    if not isinstance(depth, int) or depth < 0:
        raise ValueError("depth must be a nonnegative integer")
    return 0 if depth == 0 else 2 * depth - 1


def compensation(depth: int) -> dict[int, mp.mpf]:
    valuation(depth)
    out = {-1: mp.mpf(1)}
    if depth:
        out[0] = mp.mpf('0.5')
        for k in range(1, depth):
            out[2*k-1] = mp.bernoulli(2*k)/mp.factorial(2*k)
    return out


def kernel(x, depth: int = 0):
    """Q(x)-P_depth(x), evaluated without small-x cancellation (x>0)."""
    valuation(depth)
    if x <= 0:
        if x == 0:
            return mp.mpf('.5') if depth == 0 else mp.mpf(0)
        raise ValueError('positive real x required')
    if x < mp.mpf('.25'):
        # A convergent Bernoulli expansion; extra terms grow with precision.
        start = max(depth, 1)
        nterms = max(20, int(mp.mp.dps/2) + 10, depth+10)
        ans = mp.mpf('.5') if depth == 0 else mp.mpf(0)
        return ans + mp.fsum(mp.bernoulli(2*k)*x**(2*k-1)/mp.factorial(2*k)
                             for k in range(start, nterms+1))
    return -1/mp.expm1(-x) - mp.fsum(c*x**j for j,c in compensation(depth).items())


def laplace_moment(w, A, d=0, e=0, p=1, q=1):
    """Integral x^(w-1)e^(-Ax) h_d(qx) h_e(px) dx."""
    if mp.re(w) <= -valuation(d)-valuation(e) or mp.re(A) <= 0:
        raise ValueError('outside the stated absolute-convergence domain')
    return mp.quad(lambda x: x**(w-1)*mp.exp(-A*x)*kernel(q*x,d)*kernel(p*x,e),
                   [0, mp.mpf('.25')/max(p,q), 1, 4, mp.inf])


def K(w,A):
    """Equal-slope basic closure, away from w=1,2."""
    w,A=mp.mpmathify(w),mp.mpmathify(A)
    return (1-2/(w-1))*mp.zeta(w-1,A)+(1-A)*mp.zeta(w,A) \
           +A**(2-w)/((w-1)*(w-2))


def K_derivative_at_one(order: int, A):
    """Closed, pole-free formula for d^order K(w,A)/dw^order at w=1."""
    A=mp.mpmathify(A)
    if not isinstance(order,int) or order<0 or mp.re(A)<=0:
        raise ValueError("nonnegative integer order and Re(A)>0 required")
    l=order
    gamma_l=(mp.stieltjes(l,A) if mp.im(A)==0 else
             G_hermite(l,A)-mp.log(A)**(l+1)/(l+1))
    return (mp.zeta(0,A,derivative=l)
            -2*mp.zeta(0,A,derivative=l+1)/(l+1)
            +(1-A)*(-1)**l*gamma_l
            -A*mp.factorial(l)*mp.fsum((-mp.log(A))**j/mp.factorial(j)
                                      for j in range(l+2)))


def K_one(A):
    A=mp.mpmathify(A)
    return (mp.mpf('.5')-2*A+A*mp.log(A)-2*mp.loggamma(A)+mp.log(2*mp.pi)
            -(1-A)*mp.digamma(A))


def D_pq(w,A,p,q):
    if not all(isinstance(v,int) and v>0 for v in (p,q)):
        raise ValueError("positive integer slopes required")
    w,A=mp.mpmathify(w),mp.mpmathify(A)
    r=mp.mpf(p*q)
    return mp.fsum(mp.zeta(w-1,(A+q*i+p*j)/r)
                   +(1-(A+q*i+p*j)/r)*mp.zeta(w,(A+q*i+p*j)/r)
                   for i in range(p) for j in range(q))/r**w


def J_formula(w,A,d=0,e=0,p=1,q=1):
    """General finite closure; caller must avoid singular spectral summands."""
    w,A=mp.mpmathify(w),mp.mpmathify(A)
    P,Q=compensation(d),compensation(e)
    pp,qq=mp.mpf(p),mp.mpf(q)
    value=mp.gamma(w)*D_pq(w,A,p,q)
    value-=mp.fsum(c*pp**k*mp.gamma(w+k)*qq**(-w-k)*mp.zeta(w+k,A/q)
                   for k,c in Q.items())
    value-=mp.fsum(c*qq**j*mp.gamma(w+j)*pp**(-w-j)*mp.zeta(w+j,A/p)
                   for j,c in P.items())
    value+=mp.fsum(c*d0*qq**j*pp**k*mp.gamma(w+j+k)*A**(-w-j-k)
                   for j,c in P.items() for k,d0 in Q.items())
    return value


def K_pq_one(A,p,q):
    """Pole-free unequal-slope G0 pairing."""
    A=mp.mpmathify(A)
    r=mp.mpf(p*q)
    cs=[(A+q*i+p*j)/r for i in range(p) for j in range(q)]
    value=mp.fsum(mp.zeta(0,c)-(1-c)*mp.digamma(c)-mp.log(r)*(1-c)
                  for c in cs)/r
    value-=mp.zeta(0,A/q,derivative=1)/p+mp.zeta(0,A/p,derivative=1)/q
    value+=mp.log(q)*mp.zeta(0,A/q)/p+mp.log(p)*mp.zeta(0,A/p)/q
    value+=A/r*(mp.log(A)-1)
    return value


def G0(z):
    z=mp.mpmathify(z)
    if mp.re(z)<=0:raise ValueError("Re(z)>0 required")
    if abs(z)>60:
        return 1/(2*z)+mp.fsum(mp.bernoulli(2*k)/(2*k*z**(2*k))
                               for k in range(1,65))
    return mp.log(z)-mp.digamma(z)


def Omega(z):
    """Analytic log-Gamma Stirling remainder, not principal log(Gamma(z))."""
    z=mp.mpmathify(z)
    if mp.re(z)<=0:raise ValueError("Re(z)>0 required")
    if abs(z)>60:
        return mp.fsum(mp.bernoulli(2*k)/(2*k*(2*k-1)*z**(2*k-1))
                       for k in range(1,65))
    return mp.loggamma(z)-(z-mp.mpf('.5'))*mp.log(z)+z-mp.log(2*mp.pi)/2


def omega_pair(A):
    A=mp.mpmathify(A)
    return (A*mp.zeta(-1,A,derivative=1)-2*mp.zeta(-2,A,derivative=1)
            +(A**3/6-A**2/2+A/4)*mp.log(A)+A**3/36+A/12)


def R(depth,s,z):
    """Unnormalized compensated Hurwitz family, regular at s=0,-1,..."""
    s,z=mp.mpmathify(s),mp.mpmathify(z)
    ans=mp.zeta(s,z)-z**(1-s)/(s-1)
    if depth:
        ans-=mp.mpf('.5')*z**(-s)
        ans-=mp.fsum(mp.bernoulli(2*k)/mp.factorial(2*k)*mp.rf(s,2*k-1)
                      *z**(1-s-2*k) for k in range(1,depth))
    return ans


def primitive(depth,n,z):
    if not isinstance(n,int) or n < 0 or n >= valuation(depth):
        raise ValueError('need 0 <= n < valuation(depth)')
    return mp.diff(lambda s:R(depth,s,z),-n)/mp.factorial(n)


def bell_kernel(order, logx):
    """(-1)^m d^m [exp(u logx)/Gamma(1+u)] at zero."""
    cumulants=[mp.mpf(0),logx+mp.euler]+[
        (-1)**(r+1)*mp.factorial(r-1)*mp.zeta(r) for r in range(2,order+1)]
    vals=[mp.mpf(1)]
    for n in range(1,order+1):
        vals.append(mp.fsum(mp.binomial(n-1,j-1)*cumulants[j]*vals[n-j]
                            for j in range(1,n+1)))
    return (-1)**order*vals[order]


def _gz_laurent(k: int, C, delta=0):
    """Residue and constant term of Gamma(k+eps) zeta(k+delta+eps,C)."""
    z=k+delta
    if k <= 0:
        if z == 1:
            raise ValueError('double poles are outside this evaluator contract')
        n=-k
        c=(-1)**n/mp.factorial(n)
        v=mp.zeta(z,C)
        return c*v, c*(mp.zeta(z,C,derivative=1)+(mp.harmonic(n)-mp.euler)*v)
    if z == 1:
        return mp.gamma(k), mp.gamma(k)*(-mp.digamma(C)+mp.digamma(k))
    return mp.mpf(0),mp.gamma(k)*mp.zeta(z,C)


def _ge_laurent(k: int,C):
    """Residue and constant term of Gamma(k+eps) C^(-k-eps)."""
    if k > 0:
        return mp.mpf(0),mp.gamma(k)*C**(-k)
    n=-k
    residue=(-1)**n/mp.factorial(n)*C**n
    return residue,residue*(mp.harmonic(n)-mp.euler-mp.log(C))


def J_at_integer(w: int,A,d=0,e=0,p=1,q=1):
    """Return (finite part, residue); residue is zero in the theorem domain.

    Taylor prefactors multiplying poles are retained. No numerical small-epsilon
    subtraction is used. This is also the primitive-pairing evaluation engine.
    """
    if not isinstance(w,int):
        raise TypeError('integer w required')
    A=mp.mpmathify(A)
    if w<=-valuation(d)-valuation(e) or mp.re(A)<=0:
        raise ValueError('outside the ordinary-integral continuation domain')
    if not all(isinstance(v,int) and v>0 for v in (p,q)):
        raise ValueError('positive integer slopes required')
    pp,qq=mp.mpf(p),mp.mpf(q)
    rr=pp*qq
    residue=mp.mpf(0)
    constant=mp.mpf(0)
    def add(pair,pref=1,logder=0):
        nonlocal residue,constant
        r,c=pair
        residue+=pref*r
        constant+=pref*(c+logder*r)
    for i in range(p):
        for j in range(q):
            C=(A+qq*i+pp*j)/rr
            add(_gz_laurent(w,C,-1),rr**(-w),-mp.log(rr))
            add(_gz_laurent(w,C,0),(1-C)*rr**(-w),-mp.log(rr))
    P,Q=compensation(d),compensation(e)
    for k,c in Q.items():
        add(_gz_laurent(w+k,A/qq),-c*pp**k*qq**(-w-k),-mp.log(qq))
    for j,c in P.items():
        add(_gz_laurent(w+j,A/pp),-c*qq**j*pp**(-w-j),-mp.log(pp))
    for j,c in P.items():
        for k,d0 in Q.items():
            add(_ge_laurent(w+j+k,A),c*d0*qq**j*pp**k)
    return constant,residue


def stieltjes_cauchy(max_order: int,z,nodes: int=96,radius=None):
    """Compensated G_m(z) from spectral Cauchy coefficients of Z_(1+u).

    This avoids mpmath 1.3.0 stieltjes(n,z), whose real-part integral is not
    valid at nonreal z. A finite trapezoidal contour is a numerical check,
    not an interval-certified coefficient extraction.
    """
    if max_order<0 or nodes<=max_order:
        raise ValueError('nonnegative order and nodes > order required')
    radius=mp.mpf('.125') if radius is None else mp.mpf(radius)
    values=[]
    roots=[mp.exp(2j*mp.pi*k/nodes) for k in range(nodes)]
    for root in roots:
        u=radius*root
        values.append(mp.zeta(1+u,z)-z**(-u)/u)
    return [(-1)**m*mp.factorial(m)*mp.fsum(v/root**m for v,root in zip(values,roots))
             /(nodes*radius**m) for m in range(max_order+1)]


def G_hermite(order: int,z):
    """Complex-safe Hermite formula for compensated Stieltjes G_order(z)."""
    if order<0 or int(order)!=order or mp.re(z)<=0:
        raise ValueError('nonnegative integer order and Re(z)>0 required')
    if order==0:
        integrand=lambda t:2*t/((z*z+t*t)*mp.expm1(2*mp.pi*t))
    else:
        integrand=lambda t:1j*(mp.log(z+1j*t)**order/(z+1j*t)
                               -mp.log(z-1j*t)**order/(z-1j*t))/mp.expm1(2*mp.pi*t)
    return mp.log(z)**order/(2*z)+mp.quad(integrand,[0,1,mp.inf])
