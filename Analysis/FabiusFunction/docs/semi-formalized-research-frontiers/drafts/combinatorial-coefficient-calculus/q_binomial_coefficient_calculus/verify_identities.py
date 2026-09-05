#!/usr/bin/env python3
"""Exact, deterministic checks for q-Binomial Coefficient Calculus.

Python 3.9+; standard library only.  No floating-point comparisons, network
access, symbolic algebra package, or external data are used.  These finite
checks audit indices and normalizations; the article contains the proofs.
Run: python verify_identities.py
"""
from fractions import Fraction as F
from functools import lru_cache
from math import comb, factorial
from collections import OrderedDict

COUNTS = OrderedDict()

def check(group, actual, expected):
    if actual != expected:
        raise AssertionError(f'{group}: {actual!r} != {expected!r}')
    COUNTS[group] = COUNTS.get(group, 0) + 1

def prod(xs):
    r = F(1)
    for x in xs:
        r *= x
    return r

def trim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return tuple(a) if a else (0,)

def add(a, b):
    return trim([(a[i] if i < len(a) else 0) +
                 (b[i] if i < len(b) else 0)
                 for i in range(max(len(a), len(b)))])

def scale(a, s):
    return trim([s*x for x in a])

def mul(a, b, degree=None):
    n = len(a)+len(b)-1
    if degree is not None:
        n = min(n, degree+1)
    c = [F(0)]*n
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            if i+j < n:
                c[i+j] += x*y
    return trim(c)

def power(a, n, degree=None):
    c = (F(1),)
    for _ in range(n):
        c = mul(c, a, degree)
    return c

def compose(a, b, degree):
    c = (F(0),)
    for x in reversed(a):
        c = add(mul(c, b, degree), (x,))
    return trim(c[:degree+1])

def peval(a, x):
    v = 0
    for y in reversed(a):
        v = v*x+y
    return v

def pdiv(a, b):
    a = list(map(F, trim(a)))
    b = trim(b)
    if b == (0,):
        raise ZeroDivisionError('zero polynomial')
    out = [F(0)]*max(1, len(a)-len(b)+1)
    while len(a) >= len(b) and any(a):
        j = len(a)-len(b)
        c = a[-1]/b[-1]
        out[j] += c
        for i, x in enumerate(b):
            a[i+j] -= c*x
        a = list(trim(a))
    return trim(out), trim(a)

@lru_cache(None)
def gp(n, k):
    """Gaussian polynomial, using polynomial Pascal addition (no division)."""
    if k < 0 or k > n:
        return (0,)
    if k == 0 or k == n:
        return (1,)
    return add(gp(n-1, k), (0,)*(n-k)+gp(n-1, k-1))

def gb(n, k, q):
    return peval(gp(n, k), q) if n >= 0 else F(0)

def qi(n, q):
    return sum((q**j for j in range(n)), F(0))

def qfac(n, q):
    return prod(qi(j, q) for j in range(1, n+1))

def poch(a, q, n):
    return prod(1-a*q**j for j in range(n))

def bell(xs):
    """Y_n(x_1,...,x_n), computed independently by the pointing recurrence."""
    ys = [F(1)]
    for n in range(1, len(xs)+1):
        ys.append(sum((comb(n-1,j-1)*xs[j-1]*ys[n-j]
                       for j in range(1,n+1)), F(0)))
    return ys[-1]

def partitions(n, cap=None):
    """Multiplicity vectors (m_1,...,m_cap) with sum j*m_j=n."""
    if cap is None:
        cap = n
    if cap == 0:
        if n == 0:
            yield ()
        return
    for m in range(n//cap+1):
        for v in partitions(n-m*cap, cap-1):
            yield v+(m,)

def bell_finite(xs):
    n = len(xs)
    return factorial(n)*sum((prod((F(x, factorial(j))**m)/factorial(m)
        for j,(x,m) in enumerate(zip(xs,v),1)) for v in partitions(n)), F(0))

@lru_cache(None)
def stir(n, k):
    if n == k == 0:
        return 1
    if k <= 0 or k > n:
        return 0
    return k*stir(n-1,k)+stir(n-1,k-1)

@lru_cache(None)
def bern(n):
    return sum((F((-1)**k*factorial(k)*stir(n,k), k+1)
                for k in range(n+1)), F(0))

def sq(n,k,q):
    row = [F(1)]
    for i in range(1,n+1):
        row = [F(0)]+[qi(j,q)*(row[j] if j<len(row) else 0)+row[j-1]
                       for j in range(1,i+1)]
    return row[k] if 0<=k<=n else F(0)

def cumulants(n,k,r):
    m=n-k
    out=[]
    for s in range(1,r+1):
        delta=sum((m+j)**s-j**s for j in range(1,k+1))
        out.append(F(delta,2) if s==1 else bern(s)*F(delta,s))
    return out

@lru_cache(None)
def eulerian(n):
    # A_0(u)=1; A_n(u)=sum_{j=0}^{n-1}<n,j>u^j for n>=1.
    if n==0:
        return (1,)
    prev=eulerian(n-1)
    return trim([(j+1)*(prev[j] if j<len(prev) else 0)+
                 (n-j)*(prev[j-1] if j>0 else 0) for j in range(n)])

def li_nonpositive(s,u):
    """Li_{-s}(u), s>=0, as an exact rational function."""
    return u*peval(eulerian(s),u)/(1-u)**(s+1)

@lru_cache(None)
def cyclo(n):
    a=(-1,)+(0,)*(n-1)+(1,)
    for d in range(1,n):
        if n%d==0:
            a,rem=pdiv(a,cyclo(d))
            assert rem==(0,)
    return a

def root_jets_minus_one(n,k,rmax):
    m=n-k
    c=F(1);nu=0;lam=[F(0)]*rmax
    for sign, exponents in ((1,range(m+1,n+1)),(-1,range(1,k+1))):
        for a in exponents:
            u=F((-1)**a)
            if a%2==0:
                nu+=sign
                c*=F(-a)**sign
                eta=[F(a,2)]+[bern(r)*F(a**r,r) for r in range(2,rmax+1)]
            else:
                c*=F(1-u)**sign
                eta=[-a**r*li_nonpositive(r-1,u) for r in range(1,rmax+1)]
            lam=[x+sign*y for x,y in zip(lam,eta)]
    return nu,c,lam

def qder(p,q):
    return trim([p[j]*qi(j,q) for j in range(1,len(p))])

def qder_n(p,n,q):
    for _ in range(n):
        p=qder(p,q)
    return p

def cyclotomic_jet_checks():
    """Audit all local jets in exact Q[zeta_d], not floating-point complex numbers.

    Elements are rational polynomials reduced modulo Phi_d.  For u of exact
    order L>1, (1-u)^-1 = -(sum_{j=1}^{L-1} j*u^j)/L.  This finite identity
    avoids both numerical division and a dependency on a computer-algebra system.
    """
    from math import gcd
    for d in range(3, 9):
        modulus = cyclo(d)
        one = (F(1),)
        zero = (F(0),)
        def cmul(a, b):
            return pdiv(mul(a, b), modulus)[1]
        def cpow(a, n):
            result = one
            for _ in range(n):
                result = cmul(result, a)
            return result
        roots = [pdiv((0,)*j+(1,), modulus)[1] for j in range(d)]
        def cpoly(a, u):
            result = zero
            for x in reversed(a):
                result = add(cmul(result, u), (x,))
            return result
        # Every factor with a given exponent is reused in many Gaussian products.
        data = {}
        for a in range(1, 10):
            if a % d == 0:
                c, invc = (F(-a),), (F(-1, a),)
                eta = [(F(a, 2),)] + [(bern(r)*F(a**r,r),)
                                              for r in range(2, 8)]
            else:
                u = roots[a % d]
                order = d // gcd(d, a)
                c = add(one, scale(u, -1))
                invc = zero
                for j in range(1, order):
                    invc = add(invc, scale(cpow(u,j), F(-j,order)))
                check('Cyclotomic inverse-factor certificate', cmul(c,invc), one)
                eta = []
                for r in range(1, 8):
                    li = cmul(cmul(u,cpoly(eulerian(r-1),u)),cpow(invc,r))
                    eta.append(scale(li, -a**r))
            data[a] = (c, invc, eta)
        for n in range(10):
            for k in range(n+1):
                nu = n//d-k//d-(n-k)//d
                constant = one
                lam = [zero]*7
                for sign, exponents in ((1,range(n-k+1,n+1)),(-1,range(1,k+1))):
                    for a in exponents:
                        c, invc, eta = data[a]
                        constant = cmul(constant, c if sign==1 else invc)
                        lam = [add(x,scale(y,sign)) for x,y in zip(lam,eta)]
                ys = [one]
                for r in range(1,8):
                    val = zero
                    for j in range(1,r+1):
                        val = add(val,scale(cmul(lam[j-1],ys[r-j]),comb(r-1,j-1)))
                    ys.append(val)
                p = gp(n,k)
                for r in range(8):
                    actual = zero
                    for j,c in enumerate(p):
                        actual = add(actual,scale(roots[j%d],c*j**r))
                    expected = zero if r<nu else scale(cmul(constant,ys[r-nu]),
                                                       F(factorial(r),factorial(r-nu)))
                    check('All-root jets in exact cyclotomic fields',actual,expected)


def additional_coefficient_checks():
    """Finite index weights, repeated-root filters, and normalized composition."""
    for q in (F(1,2),F(2,3),F(2)):
        for N in range(1,8):
            z = F(2,5)
            for r in range(8):
                actual = sum((k**r*q**(k*(k-1)//2)*gb(N,k,q)*z**k
                              for k in range(N+1)),F(0))
                kernels = [-sum((li_nonpositive(s-1,-z*q**j) for j in range(N)),F(0))
                           for s in range(1,r+1)]
                check('Polynomially weighted Gaussian sums',actual,poch(-z,q,N)*bell(kernels))
            for r in range(1,9):
                actual = sum(((-1)**k*q**(k*(k-1)//2)*gb(N,k,q)*
                              (F(factorial(k),factorial(k-r)) if k>=r else 0)
                              for k in range(N+1)),F(0))
                kernels = [-factorial(s-1)*sum((q**(j*s)/(1-q**j)**s
                                        for j in range(1,N)),F(0)) for s in range(1,r)]
                check('Alternating factorial moments',actual,
                      -r*poch(q,q,N-1)*bell(kernels))
        # Normalized Bell composition: compare the finite multiplicity sum
        # against direct truncated ordinary substitution.
        cap = 7
        aa = [F((-1)**j*(j+1)) for j in range(cap+1)]
        bb = [F(0)]+[F(j+2,j+1) for j in range(1,cap+1)]
        an = [x/qfac(j,q) for j,x in enumerate(aa)]
        bn = [x/qfac(j,q) for j,x in enumerate(bb)]
        direct = compose(an,bn,cap)
        for n in range(cap+1):
            coeff = F(0)
            for k in range(n+1):
                weighted = qfac(n,q)*F(factorial(k),1)/qfac(k,q)*sum((
                    prod((bb[j]/qfac(j,q))**v[j-1]/factorial(v[j-1])
                         for j in range(1,n+1))
                    for v in partitions(n) if sum(v)==k),F(0))
                coeff += aa[k]*weighted
            check('Weighted Bell ordinary composition',coeff,
                  qfac(n,q)*(direct[n] if n<len(direct) else 0))
        # Repeated spectral roots, including the exact Bell coefficient formula.
        lam = [q,q*q]
        mult = [2,3]
        p = (F(1),)
        for x,s in zip(lam,mult):
            p = mul(p,power((-x/(1-x),1/(1-x)),s))
        c0 = prod((-x/(1-x))**s for x,s in zip(lam,mult))
        for ell in range(9):
            kernels = [-factorial(r-1)*sum(s*x**(-r) for x,s in zip(lam,mult))
                       for r in range(1,ell+1)]
            check('Confluent-filter Bell coefficients',
                  p[ell] if ell<len(p) else 0,c0*bell(kernels)/factorial(ell))
        for beta,s in enumerate(mult,1):
            for r in range(s):
                # After dividing out (log q)^r, this is theta_z^r p(q^beta).
                actual = sum((c*j**r*q**(j*beta) for j,c in enumerate(p)),F(0))
                check('Confluent geometric-logarithmic cancellation',actual,0)


def main():
    qs=[F(1,2),F(2,3),F(2),F(-2)]
    for q in qs:
        for n in range(11):
            for k in range(n+1):
                check('Gaussian product / polynomial',gb(n,k,q),
                      poch(q,q,n)/(poch(q,q,k)*poch(q,q,n-k)))
                check('Reciprocity',gb(n,k,1/q),q**(-k*(n-k))*gb(n,k,q))
            p=(F(1),)
            for j in range(n): p=mul(p,(1,-q**j))
            check('Finite q-binomial theorem',p,trim([(-1)**k*q**(k*(k-1)//2)*gb(n,k,q)
                                                    for k in range(n+1)]))
            for j in range(n+1):
                v=sum(((-1)**(n-k)*q**((n-k)*(n-k-1)//2)*gb(n,k,q)*gb(k,j,q)
                       for k in range(j,n+1)), F(0))
                check('Gaussian inversion',v,int(n==j))
        for n in range(6):
            for m in range(6):
                for r in range(n+m+1):
                    v=sum((q**((n-k)*(r-k))*gb(n,k,q)*gb(m,r-k,q)
                           for k in range(max(0,r-m),min(n,r)+1)),F(0))
                    check('q-Vandermonde',v,gb(n+m,r,q))
        for n in range(1,8):
            for p in range(9):
                lhs=sum(((-1)**(k-1)*q**(k*(k-1)//2+k*p)*gb(n,k,q)/(1-q**k)**p
                         for k in range(1,n+1)),F(0))
                xs=[factorial(j-1)*sum(((q**k/(1-q**k))**j for k in range(1,n+1)),F(0))
                    for j in range(1,p+1)]
                check('Dilcher / complete symmetric / Bell',lhs,bell(xs)/factorial(p))
            for k in range(n+1):
                sn=sq(n,k,q)
                explicit=q**(-k*(k-1)//2)/qfac(k,q)*sum((
                    (-1)**(k-j)*q**((k-j)*(k-j-1)//2)*gb(k,j,q)*qi(j,q)**n
                    for j in range(k+1)),F(0))
                check('q-Stirling explicit formula',sn,explicit)
                xs=[factorial(r-1)*sum((qi(j,q)**r for j in range(k+1)),F(0))
                    for r in range(1,n-k+1)]
                check('q-Stirling Bell formula',sn,bell(xs)/factorial(n-k))
            for r in range(7):
                rhs=sum((q**(k*(k-1)//2)*sq(r,k,q)*qfac(k,q)*gb(n,k,q)
                         for k in range(min(r,n)+1)),F(0))
                check('q-factorial moment identity',qi(n,q)**r,rhs)
            for m in range(n+5):
                v=sum(((-1)**j*q**(j*(j-1)//2-(n-1)*j)*gb(n,j,q)*q**(j*m)
                       for j in range(n+1)),F(0))
                check('Gaussian spectral stencil',v,poch(q**(m-n+1),q,n))
        for n in range(7):
            a=F(3,2); b=F(-3,2); c=F(-5,3)
            v=sum((gb(n,j,q)*a**j*poch(b,q,j)*poch(a,q,n-j) for j in range(n+1)),F(0))
            check('Pochhammer convolution',v,poch(a*b,q,n))
            v1=sum((poch(q**(-n),q,j)*poch(a,q,j)*q**j/(poch(q,q,j)*poch(c,q,j))
                    for j in range(n+1)),F(0))
            v2=sum((poch(q**(-n),q,j)*poch(a,q,j)*(c*q**n/a)**j/(poch(q,q,j)*poch(c,q,j))
                    for j in range(n+1)),F(0))
            check('q-Chu-Vandermonde (argument q)',v1,a**n*poch(c/a,q,n)/poch(c,q,n))
            check('q-Chu-Vandermonde (argument c*q^N/a)',v2,poch(c/a,q,n)/poch(c,q,n))
        f=(F(3),F(-2),F(5),F(1),F(-1));g=(F(2),F(1),F(-4))
        a=F(3,2)
        reconstruction=(F(0),);basis=(F(1),)
        for n in range(len(f)):
            reconstruction=add(reconstruction,scale(basis,peval(qder_n(f,n,q),a)/qfac(n,q)))
            basis=mul(basis,(-a*q**n,1))
        check('q-Taylor reconstruction',reconstruction,f)
        for n in range(7):
            left=qder_n(mul(f,g),n,q);right=(F(0),)
            for k in range(n+1):
                df=qder_n(f,k,q)
                df=tuple(c*q**((n-k)*j) for j,c in enumerate(df))
                right=add(right,scale(mul(df,qder_n(g,n-k,q)),gb(n,k,q)))
            check('Jackson q-Leibniz',left,right)
        # Product exponent coefficients, two independent computations.
        blocks=[(F(2),3,2),(F(-1),2,3)]
        full=(F(1),)
        for a,N,alpha in blocks:
            for i in range(N):
                full=mul(full,tuple(F(comb(alpha+r-1,r))*(a*q**i)**r for r in range(10)),9)
        for r in range(10):
            xs=[factorial(j-1)*sum((alpha*a**j*qi(N,q**j) for a,N,alpha in blocks),F(0))
                for j in range(1,r+1)]
            check('Geometric-product Bell master formula',full[r],bell(xs)/factorial(r))
    for n in range(13):
        for k in range(n+1):
            p=gp(n,k)
            for r in range(9):
                moment=sum((F(c)*i**r for i,c in enumerate(p)),F(0))
                check('Bernoulli cumulants / polynomial moments',moment,
                      comb(n,k)*bell(cumulants(n,k,r)))
                A=[sum(d for d in range(1,k+1) if j%d==0)-
                   sum(d for d in range(n-k+1,n+1) if j%d==0) for j in range(1,r+1)]
                check('Divisor-sum coefficient formula',p[r] if r<len(p) else 0,
                      bell([factorial(j-1)*a for j,a in enumerate(A,1)])/factorial(r))
            nu,c,lam=root_jets_minus_one(n,k,9)
            for r in range(10):
                moment=sum((F(v)*(-1)**j*j**r for j,v in enumerate(p)),F(0))
                pred=F(0) if r<nu else c*F(factorial(r),factorial(r-nu))*bell(lam[:r-nu])
                check('Deflated root-of-unity jets at -1',moment,pred)
            fact=(1,)
            for d in range(2,n+1):
                e=n//d-k//d-(n-k)//d
                check('Cyclotomic multiplicity is 0 or 1',e in (0,1),True)
                if e: fact=mul(fact,cyclo(d))
            check('Cyclotomic factorization',fact,p)
            for d in range(2,9):
                a,b=divmod(n,d);r,s=divmod(k,d)
                rhs=scale(gp(b,s),comb(a,r))
                _,rem=pdiv(add(p,scale(rhs,-1)),cyclo(d))
                check('q-Lucas polynomial congruence',rem,(0,))
    for q in [F(1,2),F(1,4),F(2,3)]:
        for N in range(13):
            weights=[(-1)**(N-j)*q**((N-j)*(N-j+1)//2)*gb(N,j,q)/poch(q,q,N)
                     for j in range(N+1)]
            check('Richardson constant preservation',sum(weights),1)
            check('Richardson exact noise norm',sum(map(abs,weights)),poch(-q,q,N)/poch(q,q,N))
            for m in range(1,N+7):
                actual=sum((w*q**(j*m) for j,w in enumerate(weights)),F(0))
                expected=F(0) if m<=N else (-1)**N*q**(N*(N+1)//2)*gb(m-1,N,q)
                check('Richardson complete error response',actual,expected)
    for q in [F(1,2),F(2)]:
        for n in range(8):
            for k in range(n+1):
                for ell in range(n+1):
                    rhs=sum((q**((r-k)*(r-ell))*gb(n,r,q)*gb(r,k,q)*gb(k,k+ell-r,q)
                             for r in range(max(k,ell),min(n,k+ell)+1)),F(0))
                    check('Gaussian product linearization',gb(n,k,q)*gb(n,ell,q),rhs)
        # Lagrange inversion, ordinary substitution computed by fixed-point iteration.
        for M in range(1,4):
            phi=tuple(gb(M+r-1,r,q) for r in range(10))
            y=(F(0),)
            for _ in range(10): y=((F(0),)+compose(phi,y,8))[:10]
            for n in range(1,10):
                xs=[n*factorial(j-1)*qi(M,q**j) for j in range(1,n)]
                actual=y[n] if n<len(y) else 0
                check('Lagrange inversion with q-products',actual,bell(xs)/factorial(n))
    for n in range(11):
        xs=[F((-1)**j*(j+2),j+1) for j in range(n)]
        check('Bell finite-sum normalization',bell(xs),bell_finite(xs))
    for n in range(1,9):
        # All-order derivatives of the central q-Vandermonde identity.
        for r in range(7):
            lhs=comb(2*n,n)*bell(cumulants(2*n,n,r))
            rhs=F(0)
            for k in range(n+1):
                ks=[2*x for x in cumulants(n,k,r)]
                if r: ks[0]+=k*k
                rhs+=comb(n,k)**2*bell(ks)
            check('Differentiated central Vandermonde',lhs,rhs)
    cyclotomic_jet_checks()
    additional_coefficient_checks()
    print('q-Binomial Coefficient Calculus: exact validation report')
    print('Python standard library; exact integers and fractions; no numerical tolerance.')
    print()
    for name,n in COUNTS.items(): print(f'PASS  {name}: {n} checks')
    print(f'\nTOTAL: {sum(COUNTS.values())} exact checks in {len(COUNTS)} groups; all passed.')
    print('Finite testing is an audit, not a replacement for the proofs in the article.')

if __name__=='__main__':
    main()
