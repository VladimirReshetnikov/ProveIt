#!/usr/bin/env python3
"""Reproducible checks for Gaussian Coefficients in Coefficient Calculus.

The core checks use exact fractions and integer polynomials (standard library).
They compare the article's finite formulae against independent products,
recurrences, interpolation, or direct enumeration.  These are finite checks,
not substitutes for the proofs in the article.  An optional final experiment
uses mpmath at 70 digits to check the double-scaling remainder orders.

Run: python3 verify_identities.py
No network access, data files, or computer-algebra package is required.
"""
from __future__ import annotations

from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, permutations, product
from math import comb, factorial, prod
from typing import Iterable, Sequence

COUNTS: dict[str, int] = defaultdict(int)


def check(group: str, left, right, context: str = "") -> None:
    if left != right:
        raise AssertionError(f"{group}: {context}\nleft={left}\nright={right}")
    COUNTS[group] += 1


def trim(p: Sequence) -> tuple:
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return tuple(p or [0])


def add(p: Sequence, r: Sequence) -> tuple:
    return trim([(p[j] if j < len(p) else 0) +
                 (r[j] if j < len(r) else 0)
                 for j in range(max(len(p), len(r)))])


def scale(p: Sequence, c) -> tuple:
    return trim([c * v for v in p])


def mul(p: Sequence, r: Sequence, degree: int | None = None) -> tuple:
    n = len(p) + len(r) - 2
    if degree is not None:
        n = min(n, degree)
    a = [0] * (n + 1)
    for i, u in enumerate(p):
        for j, v in enumerate(r):
            if i + j <= n:
                a[i + j] += u * v
    return trim(a)


def power(p: Sequence, m: int, degree: int | None = None) -> tuple:
    if m < 0:
        if degree is None:
            raise ValueError("A negative series power needs a truncation degree")
        return power(inverse(p, degree), -m, degree)
    a = (1,)
    for _ in range(m):
        a = mul(a, p, degree)
    return a


def coeff(p: Sequence, j: int):
    return p[j] if 0 <= j < len(p) else 0


def evaluate(p: Sequence, x):
    a = 0
    for c in reversed(p):
        a = a*x + c
    return a


def inverse(p: Sequence, n: int) -> tuple:
    if not p or p[0] == 0:
        raise ValueError("Series constant term must be nonzero")
    a = [F(1, 1)/p[0]]
    for j in range(1, n+1):
        a.append(-sum(coeff(p, i)*a[j-i] for i in range(1, j+1))/p[0])
    return tuple(a)


def compose(p: Sequence, r: Sequence, degree: int) -> tuple:
    out = (0,)
    for a in reversed(p):
        out = add(mul(out, r, degree), (a,))
    return trim(out[:degree+1])


def exp_series(p: Sequence, n: int) -> tuple:
    if coeff(p, 0) != 0:
        raise ValueError("Only exponentials with zero logarithmic constant")
    a = [F(1)]
    for m in range(1, n+1):
        a.append(sum(j*coeff(p, j)*a[m-j] for j in range(1, m+1))/m)
    return tuple(a)


def polynomial_remainder(p: Sequence, divisor: Sequence) -> tuple:
    a = list(map(F, p))
    d = trim(divisor)
    while len(a) >= len(d) and any(a):
        c = a[-1] / d[-1]
        s = len(a) - len(d)
        for j, v in enumerate(d):
            a[s+j] -= c*v
        a = list(trim(a))
    return trim(a)


def exact_quotient(p: Sequence, divisor: Sequence) -> tuple:
    a = list(map(F, p)); d = trim(divisor)
    out = [F(0)] * max(1, len(a)-len(d)+1)
    while len(a) >= len(d) and any(a):
        s = len(a)-len(d); c = a[-1]/d[-1]; out[s] += c
        for j, v in enumerate(d):
            a[s+j] -= c*v
        a = list(trim(a))
    if any(a):
        raise ValueError("Polynomial quotient is not exact")
    return trim(out)


@lru_cache(None)
def gaussian_poly(n: int, k: int) -> tuple[int, ...]:
    """Polynomial Pascal recurrence, not the rational product."""
    if n < 0 or k < 0 or k > n:
        return (0,)
    if k in (0, n):
        return (1,)
    return add(gaussian_poly(n-1, k-1),
               (0,)*k + gaussian_poly(n-1, k))


def qnum(q: F, n: int) -> F:
    return sum((q**i for i in range(n)), F(0))


def qfac(q: F, n: int) -> F:
    return prod((qnum(q, i) for i in range(1, n+1)), start=F(1))


def poch(a: F, q: F, n: int) -> F:
    return prod((1-a*q**i for i in range(n)), start=F(1))


def gauss(q: F, n: int, k: int) -> F:
    if n < 0 or k < 0 or k > n:
        return F(0)
    if q == 1:
        return F(comb(n, k))
    return poch(q**(n-k+1), q, k)/poch(q, q, k)


@lru_cache(None)
def profiles(n: int) -> tuple[tuple[int, ...], ...]:
    """All nonnegative m with sum(j*m_j)=n; independent of recurrences tested."""
    if n == 0:
        return ((),)
    out = []
    def visit(j: int, rest: int, prefix: list[int]) -> None:
        if j > n:
            if rest == 0:
                out.append(tuple(prefix))
            return
        for m in range(rest//j+1):
            visit(j+1, rest-j*m, prefix+[m])
    visit(1, n, [])
    return tuple(out)


def bell(xs: Sequence, n: int | None = None) -> F:
    """Closed complete Bell polynomial profile, x_r supplied at index r-1."""
    if n is None:
        n = len(xs)
    total = F(0)
    for m in profiles(n):
        term = F(factorial(n))
        for j, mj in enumerate(m, 1):
            if mj:
                term *= F(xs[j-1], factorial(j))**mj/factorial(mj)
        total += term
    return total


def node_stirling(nodes: Sequence, nmax: int) -> list[list]:
    rows = [[F(1)]+[F(0)]*nmax]
    for n in range(nmax):
        old = rows[-1]
        rows.append([(old[k-1] if k else 0)+nodes[k]*old[k]
                     for k in range(nmax+1)])
    return rows


def ordinary_stirling(nmax: int) -> tuple[list[list], list[list]]:
    second = node_stirling(list(map(F, range(nmax+1))), nmax)
    first = [[F(1)]+[F(0)]*nmax]
    for n in range(nmax):
        first.append([(first[n][k-1] if k else 0)-n*first[n][k]
                      for k in range(nmax+1)])
    return second, first


def dd(values: Sequence, nodes: Sequence):
    """Barycentric formula, independent of the Jackson operator."""
    return sum(values[j]/prod((nodes[j]-nodes[i]
                              for i in range(len(nodes)) if i != j), start=F(1))
               for j in range(len(nodes)))


def dq(p: Sequence, q: F, n: int = 1) -> tuple:
    out = tuple(p)
    for _ in range(n):
        out = trim([out[j]*qnum(q, j) for j in range(1, len(out))])
    return out


def reversion_from_phi(phi: Sequence, n: int) -> tuple:
    """Independent fixed-point iteration; enough iterations determine n coefficients."""
    g = (0,)
    for _ in range(n):
        g = (0,) + compose(phi, g, n-1)
        g = trim(g[:n+1])
    return g


def run_exact() -> None:
    qs = (F(1, 2), F(2, 3), F(2))
    # Gaussian products, polynomiality, reciprocity, subset weights.
    for q in qs:
        for n in range(10):
            for k in range(n+1):
                check("Gaussian/product/reciprocity", evaluate(gaussian_poly(n,k), q),
                      gauss(q,n,k), f"q={q},n={n},k={k}")
                check("Gaussian/product/reciprocity", gauss(q,n,k),
                      q**(k*(n-k))*gauss(1/q,n,k))
                if n <= 7:
                    check("Subset enumeration", gauss(q,n,k),
                          sum((q**(sum(a)-k*(k-1)//2)
                               for a in combinations(range(n),k)),F(0)))
        for N in range(7):
            p = (F(1),)
            for j in range(N):
                p = mul(p,(1,-q**j))
            for k in range(N+1):
                check("Finite products", coeff(p,k),
                      (-1)**k*q**(k*(k-1)//2)*gauss(q,N,k))
            if N:
                inv = inverse(p,7)
                for k in range(8):
                    check("Finite reciprocal products",inv[k],gauss(q,N+k-1,k))
        for m in range(5):
            for n in range(5):
                for k in range(m+n+1):
                    rhs = sum((q**((m-j)*(k-j))*gauss(q,m,j)*gauss(q,n,k-j)
                               for j in range(max(0,k-n),min(m,k)+1)),F(0))
                    check("q-Vandermonde",rhs,gauss(q,m+n,k))
        seq = [F((-1)**k*(k*k+1),k+1) for k in range(10)]
        b = [sum(gauss(q,n,k)*seq[k] for k in range(n+1)) for n in range(10)]
        for n in range(10):
            rhs = sum((-1)**(n-k)*q**((n-k)*(n-k-1)//2)*gauss(q,n,k)*b[k]
                      for k in range(n+1))
            check("Gaussian inversion",rhs,seq[n])
        for n in range(7):
            a,c = F(1,3),F(1,7)
            terms = [poch(q**(-n),q,j)*poch(a,q,j)/
                     (poch(q,q,j)*poch(c,q,j)) for j in range(n+1)]
            check("Terminating q-Chu sums",sum(terms[j]*(c*q**n/a)**j for j in range(n+1)),
                  poch(c/a,q,n)/poch(c,q,n))
            check("Terminating q-Chu sums",sum(terms[j]*q**j for j in range(n+1)),
                  a**n*poch(c/a,q,n)/poch(c,q,n))
        for m in range(1,5):
            for k in range(7):
                neg = poch(q**(-m-k+1),q,k)/poch(q,q,k)
                check("Negative upper arguments",neg,
                      (-1)**k*q**(-m*k-k*(k-1)//2)*gauss(q,m+k-1,k))
        # Newton bases and affine geometric master.
        for n in range(8):
            p=(F(1),); out=(F(0),)
            for k in range(n+1):
                out=add(out,scale(p,gauss(q,n,k)))
                p=mul(p,(-q**k,1))
            check("Geometric Newton basis",out,(0,)*n+(1,))
        A,B=F(1,3),F(2,5)
        tab=node_stirling([A+B*q**j for j in range(9)],8)
        st=node_stirling([qnum(q,j) for j in range(9)],8)
        col=node_stirling([qnum(q,1+2*j) for j in range(9)],8)
        for n in range(9):
            for k in range(n+1):
                check("Affine geometric nodes",tab[n][k],
                      sum(comb(n,d)*A**(n-d)*B**(d-k)*gauss(q,d,k)
                          for d in range(k,n+1)))
                check("q-Stirling Gaussian formula",st[n][k],
                      (1-q)**(k-n)*sum((-1)**(d-k)*comb(n,d)*gauss(q,d,k)
                                             for d in range(k,n+1)))
                spectral=q**(-k*(k-1)//2)/qfac(q,k)*sum(
                    (-1)**(k-j)*q**((k-j)*(k-j-1)//2)*gauss(q,k,j)*qnum(q,j)**n
                    for j in range(k+1))
                check("q-Stirling spectral formula",spectral,st[n][k])
                check("Colored/type-B nodes",col[n][k],
                      (1-q)**(k-n)*sum(comb(n,d)*(-q)**(d-k)*gauss(q*q,d,k)
                                             for d in range(k,n+1)))
                basis=(F(1),)
                for j in range(n):
                    basis=mul(basis,(-qnum(q,j),1))
                first=(1-q)**(k-n)*sum((-1)**(d-k)*comb(d,k)*
                         q**((n-d)*(n-d-1)//2)*gauss(q,n,d) for d in range(k,n+1))
                check("First-kind q-Stirling formula",first,coeff(basis,k))
        # Normal ordering tested on a monomial, independently of coefficient recurrence.
        for n in range(7):
            for m in range(8):
                rhs=sum(q**(k*(k-1)//2)*st[n][k]*
                        prod((qnum(q,m-j) for j in range(k)),start=F(1))
                        for k in range(min(n,m)+1))
                check("Jackson normal ordering",rhs,qnum(q,m)**n)
        # Direct permutation enumeration defines the Eulerian polynomials.
        for n in range(1,7):
            e=[F(0)]*n
            for perm in permutations(range(n)):
                desc=[j+1 for j in range(n-1) if perm[j]>perm[j+1]]
                e[len(desc)]+=q**sum(desc)
            for j in range(n):
                explicit=sum((-1)**r*q**(r*(r-1)//2)*gauss(q,n+1,r)*
                             qnum(q,j-r+1)**n for r in range(j+1))
                check("q-Eulerian enumeration",e[j],explicit)
            for m in range(6):
                check("q-Worpitzky",qnum(q,m+1)**n,
                      sum(e[j]*gauss(q,m+n-j,n) for j in range(n)))
            for k in range(1,n+1):
                U=q**(k*(k-1)//2)*qfac(q,k)*st[n][k]
                rhs=sum(q**(k*(k-ell))*e[ell-1]*gauss(q,n-ell,k-ell)
                        for ell in range(1,k+1))
                check("Stirling-Eulerian transform",U,rhs)
            reconstructed=(0,)
            for k in range(1,n+1):
                f=(F(1),)
                for j in range(k+1,n+1):
                    f=mul(f,(1,-q**j))
                U=q**(k*(k-1)//2)*qfac(q,k)*st[n][k]
                reconstructed=add(reconstructed,(0,)*(k-1)+scale(f,U))
            check("Inverse Eulerian transform",trim(e),reconstructed)
        # Bell q-product coefficients, checked by direct series products.
        for N in range(1,6):
            p=(F(1),)
            for j in range(N):
                p=mul(p,(1,-q**j))
            pinv=inverse(p,8)
            for n in range(9):
                ps=[sum(q**(i*j) for i in range(N)) for j in range(1,n+1)]
                be=bell([(-1)**(j-1)*factorial(j-1)*ps[j-1]
                         for j in range(1,n+1)])/factorial(n)
                bh=bell([factorial(j-1)*ps[j-1] for j in range(1,n+1)])/factorial(n)
                check("Gaussian Bell identities",be,
                      q**(n*(n-1)//2)*gauss(q,N,n))
                check("Gaussian Bell identities",bh,pinv[n])
        # Mixed product (1-z)^(-2)(1-qz)^(-2)(1-z/3), independently expanded.
        base=power(mul((1,-1),(1,-q)),-2,8)
        direct=mul(base,(1,F(-1,3)),8)
        for n in range(9):
            L=[2*(1+q**j)-F(1,3)**j for j in range(1,n+1)]
            check("Mixed product Bell formula",coeff(direct,n),
                  bell([factorial(j-1)*L[j-1] for j in range(1,n+1)])/factorial(n))
        # Polynomial Jackson Taylor, product rule, finite difference, chain rule.
        f=(1,2,-1,3,0,2,1); g=(2,1,3,1)
        x=F(3,5)
        for n in range(7):
            lhs=evaluate(dq(f,q,n),x)
            rhs=sum((-1)**j*q**(j*(j-1)//2-(n-1)*j)*gauss(q,n,j)*
                    evaluate(f,q**j*x) for j in range(n+1))/((1-q)**n*x**n)
            check("Jackson finite differences",lhs,rhs)
            nodes=[x*q**j for j in range(n+1)]
            check("Jackson divided differences",lhs/qfac(q,n),
                  dd([evaluate(f,t) for t in nodes],nodes))
            lhs=evaluate(dq(mul(f,g),q,n),x)
            rhs=sum(gauss(q,n,j)*evaluate(dq(f,q,n-j),q**j*x)*
                    evaluate(dq(g,q,j),x) for j in range(n+1))
            check("Jackson Leibniz",lhs,rhs)
        taylor=(0,); pk=(1,)
        for k in range(len(f)):
            taylor=add(taylor,scale(pk,evaluate(dq(f,q,k),x)/qfac(q,k)))
            pk=mul(pk,(-x*q**k,1))
        check("Jackson Taylor",taylor,trim(f))
        outer=(1,-2,3,1); inner=(1,1,1)
        for n in range(1,6):
            nodes=[x*q**j for j in range(n+1)]
            ys=[evaluate(inner,t) for t in nodes]
            lhs=dd([evaluate(outer,y) for y in ys],nodes)
            rhs=F(0)
            for k in range(1,n+1):
                for mid in combinations(range(1,n),k-1):
                    path=(0,)+mid+(n,)
                    val=dd([evaluate(outer,ys[i]) for i in path],[ys[i] for i in path])
                    for a,b in zip(path,path[1:]):
                        val*=dd(ys[a:b+1],nodes[a:b+1])
                    rhs+=val
            check("Divided-difference chain rule",lhs,rhs)
        # Closed composition and power profiles versus ordinary series arithmetic.
        normalized=[F(0)]+[F(j+1,Q) for j,Q in
                         [(j,qfac(q,j)) for j in range(1,7)]]
        for n in range(1,7):
            for k in range(1,n+1):
                rhs=F(0)
                for p in profiles(n):
                    if sum(p)==k:
                        rhs+=F(factorial(k),prod(factorial(v) for v in p))*prod(
                            (normalized[j]**v for j,v in enumerate(p,1)),start=F(1))
                rhs*=qfac(q,n)/qfac(q,k)
                check("Normalized composition Bell profiles",rhs,
                      qfac(q,n)/qfac(q,k)*coeff(power(normalized,k,n),n))
        c32=qfac(q,3)/qfac(q,2)*coeff(power(normalized,2,3),3)
        check("Rational q-Bell normalization",c32,
              2*qnum(q,3)/qnum(q,2)*2*3)
        for N in range(1,5):
            # Ordinary compositional inverse of w*(w;q)_N.
            p=(F(1),)
            slot=(F(1),)
            for j in range(N):
                p=mul(p,(1,-q**j)); slot=mul(slot,(1,q**j))
            phi=inverse(p,8)
            rev=reversion_from_phi(phi,8)
            slot_rev=reversion_from_phi(slot,8)
            for n in range(1,9):
                L=[sum(q**(i*j) for i in range(N)) for j in range(1,n)]
                closed=bell([n*factorial(j-1)*L[j-1] for j in range(1,n)])/factorial(n)
                check("Lagrange-Bell inverses",coeff(rev,n),closed)
                check("Slot-tree Lagrange coefficients",coeff(slot_rev,n),
                      coeff(power(slot,n,n-1),n-1)/F(n))
                reversed_slot=(F(1),)
                for j in range(N):
                    reversed_slot=mul(reversed_slot,(1,q**(-j)))
                reversecoef=coeff(power(reversed_slot,n,n-1),n-1)/F(n)
                check("Slot-tree reciprocity",coeff(slot_rev,n),
                      q**((N-1)*(n-1))*reversecoef)
            check("Series inverse substitution",compose((0,)+p,rev,8),(0,1))
        # Parameter differentiation and Euler q derivatives at nonsingular q.
        S,_=ordinary_stirling(8)
        for r in range(1,7):
            x=F(1,3)
            rr=sum(factorial(ell-1)*S[r][ell]*x**ell/(1-x)**ell
                   for ell in range(1,r+1))
            # Independent power-series rational derivative using symbolic polynomials.
            # Eulerian numerator from direct permutations gives R_r.
            if r==1:
                rhs=x/(1-x)
            else:
                numerator=sum(x**(1+sum(p[j]>p[j+1] for j in range(r-2)))
                              for p in permutations(range(r-1)))
                rhs=numerator/(1-x)**r
            check("Stirling-Eulerian rational functions",rr,rhs)
        for n in range(1,9):
            for k in range(n+1):
                p=gaussian_poly(n,k)
                for m in range(1,5):
                    Ks=[]
                    for r in range(1,m+1):
                        def R(t):
                            return sum(factorial(ell-1)*S[r][ell]*t**ell/(1-t)**ell
                                       for ell in range(1,r+1))
                        Ks.append(sum(i**r*R(q**i)-(n-k+i)**r*R(q**(n-k+i))
                                      for i in range(1,k+1)))
                    lhs=sum(c*j**m*q**j for j,c in enumerate(p))
                    check("Euler-q Bell derivatives",lhs,gauss(q,n,k)*bell(Ks))
    # Bernoulli numbers from t/(e^t-1), not a named library function.
    nmax=14
    bs=inverse([F(1,factorial(j+1)) for j in range(nmax+1)],nmax)
    B=[bs[j]*factorial(j) for j in range(nmax+1)]
    _,signed=ordinary_stirling(8)
    for n in range(1,13):
        for k in range(n+1):
            p=gaussian_poly(n,k); d=k*(n-k)
            cumulants=[]
            for m in range(1,9):
                if m==1: kap=F(d,2)
                elif m%2: kap=F(0)
                else:
                    delta=(sum(j**m for j in range(1,n+1))
                           -sum(j**m for j in range(1,k+1))
                           -sum(j**m for j in range(1,n-k+1)))
                    kap=B[m]*delta/m
                cumulants.append(kap)
                raw=sum(c*j**m for j,c in enumerate(p))
                check("q=1 cumulants",raw,comb(n,k)*bell(cumulants))
                derivative=sum(c*prod(range(j-m+1,j+1)) if j>=m else 0
                               for j,c in enumerate(p))
                formula=comb(n,k)*sum(signed[m][r]*bell(cumulants[:r])
                                     for r in range(m+1))
                check("q=1 ordinary derivatives",derivative,formula)
    # Cyclotomic polynomials built from x^n-1 by exact polynomial division.
    cyclo={1:(-1,1)}
    for n in range(2,19):
        p=(-1,)+(0,)*(n-1)+(1,)
        for d in range(1,n):
            if n%d==0:
                p=exact_quotient(p,cyclo[d])
        cyclo[n]=p
    for n in range(19):
        for k in range(n+1):
            p=(1,)
            for ell in range(2,n+1):
                v=n//ell-k//ell-(n-k)//ell
                check("Cyclotomic multiplicities",v in (0,1),True)
                if v:
                    p=mul(p,cyclo[ell])
            check("Cyclotomic factorization",p,gaussian_poly(n,k))
            for ell in range(2,9):
                a,b=divmod(n,ell); c,d=divmod(k,ell)
                rhs=scale(gaussian_poly(b,d),comb(a,c))
                rem=polynomial_remainder(add(gaussian_poly(n,k),scale(rhs,-1)),cyclo[ell])
                check("q-Lucas polynomial congruences",rem,(0,))
    # Exact local jets at the nontrivial rational root of unity q=-1.
    for n in range(1,15):
        for k in range(n+1):
            p=gaussian_poly(n,k)
            nu=n//2-k//2-(n-k)//2
            hp=exact_quotient(p,(1,1)) if nu else p
            jet=compose(hp,(-1,1),6)
            h0=jet[0]
            # log(H(-1+h)/H(-1)) via its series derivative divided by the series.
            deriv=tuple((j+1)*coeff(jet,j+1) for j in range(6))
            logarithmic_derivative=mul(deriv,inverse(jet,5),5)
            cumulants=[factorial(r-1)*coeff(logarithmic_derivative,r-1)
                       for r in range(1,7)]
            for r in range(7):
                check("Root-of-unity regularized jets",coeff(jet,r),
                      h0*bell(cumulants[:r])/factorial(r))
            if nu:
                dp=sum(j*c*(-1)**(j-1) for j,c in enumerate(p) if j)
                check("Root-of-unity simple derivatives",dp,h0)
    # Additional product/derivative and normalized matrix identities.
    for q in qs:
        for N in range(1,6):
            p=(F(1),)
            for j in range(N):
                p=mul(p,(1,-q**j))
            a=F(1,7)
            jet=compose(p,(a,1),7)
            L=[-factorial(r-1)*sum(q**(j*r)/(1-a*q**j)**r for j in range(N))
               for r in range(1,8)]
            for r in range(8):
                check("Pochhammer parameter derivatives",factorial(r)*coeff(jet,r),
                      evaluate(p,a)*bell(L[:r]))
        for n in range(1,10):
            for k in range(n+1):
                finite=sum((-1)**j*q**(j*(n-k+1)+j*(j-1)//2)*gauss(q,k,j)
                           for j in range(k+1))/poch(q,q,k)
                check("Fixed-k exact exponential expansion",finite,gauss(q,n,k))
        D=6
        def riordan(g,f):
            return [[qfac(q,n)/qfac(q,k)*coeff(mul(g,power(f,k,D),D),n)
                     for k in range(D+1)] for n in range(D+1)]
        def mm(A,B):
            return [[sum(A[n][j]*B[j][k] for j in range(D+1))
                     for k in range(D+1)] for n in range(D+1)]
        g=(1,2,1); f=(0,1,1); h=(1,-1,2); ell=(0,2,-1,1)
        left=mm(riordan(g,f),riordan(h,ell))
        right=riordan(mul(g,compose(h,f,D),D),compose(ell,f,D))
        for n in range(D+1):
            for k in range(D+1):
                check("Normalized Riordan product law",left[n][k],right[n][k])
    # Gaussian filters and independent finite convolution moment calculation.
    for s in (F(1,4),F(2,5)):
        for d in range(7):
            weights=[(-1)**(d-j)*s**((d-j)*(d-j+1)//2)*gauss(s,d,j)/poch(s,s,d)
                     for j in range(d+1)]
            for r in range(12):
                rhs=F(1) if r==0 else F(0) if r<=d else \
                    (-1)**d*s**(d*(d+1)//2)*gauss(s,r-1,d)
                check("Gaussian filter residual",sum(weights[j]*s**(r*j) for j in range(d+1)),rhs)
    for q in (F(1,2),F(2,3)):
        s=q*q
        for d in range(1,6):
            cum=[F(0)]*(2*d)
            for r in range(1,d+1):
                cum[2*r-1]=F(2**(2*r)*B[2*r],2*r)*(1-q)**(2*r)/(1-q**(2*r))
            infinite=bell(cum)
            weights=[(-1)**(d-j)*s**((d-j)*(d-j+1)//2)*gauss(s,d,j)/poch(s,s,d)
                     for j in range(d+1)]
            for N in range(1,4):
                finite=[]
                for j in range(d+1):
                    # Direct product of the elementary uniform mgf, not cumulants.
                    mgf=(F(1),)
                    for i in range(N+j):
                        a=(1-q)*q**i
                        factor=tuple(a**m/F(factorial(m+1)) if m%2==0 else F(0)
                                     for m in range(2*d+1))
                        mgf=mul(mgf,factor,2*d)
                    moment=factorial(2*d)*coeff(mgf,2*d)
                    finite.append(moment)
                    fcu=[cum[r-1]*(1-q**(r*(N+j))) for r in range(1,2*d+1)]
                    check("Finite uniform moments/cumulants",moment,bell(fcu))
                check("Exact moment extrapolation",sum(w*m for w,m in zip(weights,finite)),infinite)
            if q==F(1,2) and d<=2:
                check("Rvachev moment examples",infinite,F(1,9) if d==1 else F(19,675))


def run_asymptotic_experiment() -> None:
    try:
        import mpmath as mp
    except ImportError:
        print("\nOptional double-scaling experiment skipped: install mpmath to run it.")
        return
    mp.mp.dps=70
    tau=mp.mpf('1.3'); alpha=mp.mpf(1)/3; b=1-alpha
    h=lambda x: mp.log(-mp.expm1(-tau*x)/(tau*x)) if x else mp.mpf(0)
    rate=(mp.polylog(2,mp.exp(-tau))-mp.polylog(2,mp.exp(-tau*alpha))-
          mp.polylog(2,mp.exp(-tau*b))+mp.pi**2/6)/tau
    def C(r):
        order=2*r-1
        at0=-tau/2 if r==1 else mp.mpf(0)
        return (mp.bernoulli(2*r)/(2*r*(2*r-1))*(1-alpha**(1-2*r)-b**(1-2*r))+
                mp.bernoulli(2*r)/mp.factorial(2*r)*
                (mp.diff(h,1,order)-mp.diff(h,alpha,order)-mp.diff(h,b,order)+at0))
    c1,c3,c5=C(1),C(2),C(3)
    print("\nOptional numerical experiment (mpmath, 70 decimal digits)")
    print("tau=1.3, k=n/3. R1 omits C3/n^3; R2 omits C5/n^5.")
    print(" n          n^3 R1                  n^5 R2")
    for n in (60,120,240):
        k=n//3
        exact=sum(mp.log(-mp.expm1(-tau*mp.mpf(n-k+i)/n))-
                  mp.log(-mp.expm1(-tau*mp.mpf(i)/n)) for i in range(1,k+1))
        leading=n*rate-mp.log(2*mp.pi*n*alpha*b)/2+(h(1)-h(alpha)-h(b))/2
        r1=exact-leading-c1/n; r2=r1-c3/n**3
        print(f"{n:3d}  {mp.nstr(n**3*r1,20):>24}  {mp.nstr(n**5*r2,20):>24}")
    print("Predicted limits:",mp.nstr(c3,20),mp.nstr(c5,20))
    print("Numerical agreement is evidence, not a certified error bound; the article proves the bound.")


def main() -> None:
    run_exact()
    print("EXACT CHECKS: ALL PASSED")
    for name,count in sorted(COUNTS.items()):
        print(f"{count:6d}  {name}")
    print(f"TOTAL EXACT CHECKS: {sum(COUNTS.values())}")
    run_asymptotic_experiment()


if __name__ == '__main__':
    main()
