#!/usr/bin/env python3
"""Exact, finite regression checks for q_binomial_coefficient_calculus.tex.

Requires Python 3.10+ and SymPy. No network access is used.
Run: python verify_identities.py --group all
Individual groups can be run separately; JSON reports are written beside this file.
These tests are not a proof assistant or an all-index formal verification.
"""
from __future__ import annotations

import argparse
import itertools
import json
import platform
import time
from functools import lru_cache
from pathlib import Path
from typing import Callable

import sympy as sp
from sympy.functions.combinatorial.numbers import stirling
from sympy.utilities.iterables import partitions

q = sp.Symbol("q")
x = sp.Symbol("x")
ZERO = sp.S.Zero
ONE = sp.S.One
COUNTS: dict[str, int] = {}


def check(name: str, lhs, rhs) -> None:
    lhs, rhs = sp.sympify(lhs), sp.sympify(rhs)
    if lhs.has(sp.Float) or rhs.has(sp.Float):
        raise AssertionError(f"{name}: unexpected floating-point input")
    difference = sp.cancel(sp.expand(lhs - rhs))
    if difference != 0:
        difference = sp.simplify(difference)
    if difference != 0:
        raise AssertionError(f"{name}: nonzero difference {difference}")
    COUNTS[name] = COUNTS.get(name, 0) + 1


@lru_cache(None)
def gaussian(n: int, k: int):
    """Independent polynomial definition: weighted subsets, not Pascal's rule."""
    if n < 0:
        raise ValueError("The polynomial definition requires n >= 0")
    if not 0 <= k <= n:
        return ZERO
    return sp.Add(*(q ** (sum(I) - k * (k - 1) // 2)
                    for I in itertools.combinations(range(n), k)))


def G(n: int, k: int, base=q):
    return gaussian(n, k).subs(q, base)


def qi(n: int, base=q):
    return sum((base**j for j in range(n)), ZERO)


def qfac(n: int, base=q):
    return sp.sympify(sp.prod(qi(j, base) for j in range(1, n + 1)))


def D(n: int, base=q):
    return sp.sympify(sp.prod(1 - base**j for j in range(1, n + 1)))


def poch(a, base, n: int):
    return sp.sympify(sp.prod(1 - a * base**j for j in range(n)))


@lru_cache(None)
def profiles(n: int):
    if n < 0:
        return ()
    return tuple(tuple(sorted(p.items())) for p in partitions(n))


def E(n: int, L: dict[int, sp.Expr]):
    """The finite partition kernel E_n(L) defined in the article."""
    if n < 0:
        return ZERO
    return sum((sp.prod((sp.sympify(L[j]) / j)**m / sp.factorial(m) for j, m in p)
                for p in profiles(n)), ZERO)


def bell(n: int, kap: dict[int, sp.Expr]):
    return sp.factorial(n) * E(
        n, {j: kap[j] / sp.factorial(j - 1) for j in range(1, n + 1)}
    )


def mul(a: list, b: list, degree: int) -> list:
    c = [ZERO] * (degree + 1)
    for i in range(min(len(a), degree + 1)):
        for j in range(min(len(b), degree + 1 - i)):
            c[i + j] += a[i] * b[j]
    return [sp.expand(t) for t in c]


def power(a: list, n: int, degree: int) -> list:
    ans = [ONE] + [ZERO] * degree
    for _ in range(n):
        ans = mul(ans, a, degree)
    return ans


def compose(a: list, b: list, degree: int) -> list:
    ans = [ZERO] * (degree + 1)
    p = [ONE] + [ZERO] * degree
    for ai in a[:degree + 1]:
        ans = [sp.expand(v + ai * w) for v, w in zip(ans, p)]
        p = mul(p, b, degree)
    return ans


def inverse_series(a: list, degree: int) -> list:
    """Independent triangular reciprocal, only used as a verification route."""
    if a[0] == 0:
        raise ValueError("Nonzero constant coefficient required")
    b = [ONE / a[0]] + [ZERO] * degree
    for n in range(1, degree + 1):
        b[n] = sp.cancel(-sum((a[j] * b[n-j]
                     for j in range(1, min(n, len(a)-1) + 1)), ZERO) / a[0])
    return b


def slot_power(p: int, N: int, degree: int, base=q) -> list:
    a = [base**(k*(k-1)//2) * G(N, k, base)
         for k in range(min(N, degree) + 1)]
    return power(a, p, degree)


def algebra() -> None:
    """Polynomial identities and exact rational terminating sums."""
    for N in range(9):
        prod = sp.Poly(poch(-x, q, N), x)
        for k in range(N + 2):
            check("finite theorem N<=8", prod.nth(k), q**(k*(k-1)//2)*G(N,k))
        for k in range(N + 1):
            check("reciprocity N<=8", q**(k*(N-k))*G(N,k,1/q), G(N,k))
            if N:
                check("two Pascal rules N<=8", G(N,k), G(N-1,k)+q**(N-k)*G(N-1,k-1))
                check("two Pascal rules N<=8", G(N,k), q**k*G(N-1,k)+G(N-1,k-1))
    for M in range(5):
        for N in range(5):
            for r in range(M + N + 1):
                rhs = sum((q**((M-k)*(r-k))*G(M,k)*G(N,r-k)
                     for k in range(max(0,r-N), min(M,r)+1)), ZERO)
                check("Vandermonde M,N<=4", G(M+N,r), rhs)
    for N in range(1,6):
        inv = inverse_series([sp.Poly(poch(x,q,N),x).nth(k)
                              for k in range(N+1)], 6)
        for r in range(7):
            check("reciprocal product N<=5,r<=6", inv[r], G(N+r-1,r))
            orth = sum(((-1)**k*q**(k*(k-1)//2)*G(N,k)*G(N+r-k-1,r-k)
                        for k in range(min(N,r)+1)), ZERO)
            check("product orthogonality N<=5,r<=6",orth,int(r==0))
    for n in range(8):
        for j in range(n+1):
            v = sum(((-1)**(n-k)*q**((n-k)*(n-k-1)//2)*G(n,k)*G(k,j)
                     for k in range(j,n+1)), ZERO)
            check("transform inverse n<=7", v, int(n==j))
    for base in [sp.Rational(1,2), sp.Rational(2), sp.Rational(3,5)]:
        a,c=sp.Rational(3),sp.Rational(5)
        for n in range(5):
            terms=[poch(base**(-n),base,k)*poch(a,base,k)/(D(k,base)*poch(c,base,k))
                   for k in range(n+1)]
            check("Chu first n<=4,three rational bases",sum((terms[k]*base**k for k in range(n+1)),ZERO),
                  a**n*poch(c/a,base,n)/poch(c,base,n))
            check("Chu second n<=4,three rational bases",sum((terms[k]*(c*base**n/a)**k for k in range(n+1)),ZERO),
                  poch(c/a,base,n)/poch(c,base,n))
    for n in range(8):
        for k in range(n+1):
            check("q hockey-stick n<=7",sum((q**(j-k)*G(j,k) for j in range(k,n+1)),ZERO),G(n+1,k+1))


def coefficients() -> None:
    """Master kernel, q coefficients, interpolation, composition and Jackson rule."""
    for base in [sp.Rational(1,2),sp.Rational(2)]:
        degree=8
        # (2z;q)_3^(-2) * (-z^2;q^2)_2^(3/2)
        data=[(sp.Integer(2),1,1,3,sp.Integer(-2)),
              (sp.Integer(-1),2,2,2,sp.Rational(3,2))]
        p=[ONE]+[ZERO]*degree
        L={j:ZERO for j in range(1,degree+1)}
        for a,d,h,N,alpha in data:
            for i in range(N):
                factor=[ZERO]*(degree+1)
                for k in range(degree//d+1):
                    factor[d*k]=sp.binomial(alpha,k)*(-a*base**(h*i))**k
                p=mul(p,factor,degree)
            for j in range(d,degree+1,d):
                L[j] -= d*alpha*a**(j//d)*sum((base**(h*j*i//d) for i in range(N)),ZERO)
        for n in range(degree+1):
            check("ramified master n<=8,two bases",p[n],E(n,L))
        for n in range(1,7):
            poly=x**n+2*x+3
            reconstructed=ZERO
            F=ONE
            for k in range(n+1):
                if k:
                    F*=x-qi(k-1,base)
                ck=sum(((-1)**(k-j)*base**((k-j)*(k-j-1)//2)*G(k,j,base)*poly.subs(x,qi(j,base))
                        for j in range(k+1)),ZERO)
                reconstructed+=ck*F/(base**(k*(k-1)//2)*qfac(k,base))
            check("q-integer Newton degree<=6,two bases", reconstructed,poly)
            rec_geo=ZERO
            Pg=ONE
            for k in range(n+1):
                if k:
                    Pg*=x-base**(k-1)
                Ak=sum(((-1)**j*base**(-k*j+j*(j+1)//2)*poly.subs(x,base**j)/(D(j,base)*D(k-j,base))
                        for j in range(k+1)),ZERO)
                rec_geo+=Ak*Pg
            check("geometric Newton degree<=6,two bases",rec_geo,poly)
        # q-Stirling coefficients from independent monic basis subtraction.
        for n in range(7):
            rem=x**n
            recovered={}
            for k in range(n,-1,-1):
                F=sp.prod(x-qi(i,base) for i in range(k))
                ck=sp.Poly(rem,x).nth(k)
                recovered[k]=ck
                rem=sp.expand(rem-ck*F)
            for k in range(n+1):
                ck=sum(((-1)**(k-j)*base**((k-j)*(k-j-1)//2)*G(k,j,base)*qi(j,base)**n
                        for j in range(k+1)),ZERO)/(base**(k*(k-1)//2)*qfac(k,base))
                check("q-Stirling n<=6,two bases",ck,recovered[k])
        degree=6
        f=[sp.Integer(k+1)/qfac(k,base) for k in range(degree+1)]
        g=[ZERO]+[sp.Integer(j+2)/qfac(j,base) for j in range(1,degree+1)]
        composed=compose(f,g,degree)
        for n in range(degree+1):
            out=ZERO
            for k in range(n+1):
                profsum=ZERO
                for p in profiles(n):
                    if sum(m for _,m in p)==k:
                        profsum+=sp.factorial(k)*sp.prod(g[j]**m/sp.factorial(m) for j,m in p)
                B=qfac(n,base)/qfac(k,base)*profsum
                out+=(k+1)*B
            check("q-divided Bell composition n<=6,two bases",out,qfac(n,base)*composed[n])
        def J(f):
            return sp.cancel((f-f.subs(x,base*x))/((1-base)*x))
        fpol=x**4+2*x+1
        gpol=x**3-x+2
        fd=[fpol]; gd=[gpol]; lhs=fpol*gpol
        for n in range(5):
            if n:
                fd.append(J(fd[-1]));gd.append(J(gd[-1]));lhs=J(lhs)
            rhs=sum((G(n,k,base)*fd[k].subs(x,base**(n-k)*x)*gd[n-k] for k in range(n+1)),ZERO)
            check("Jackson Leibniz n<=4,two bases",lhs,rhs)
    # Polynomial base-parameter coefficients, no numerical q specialization.
    for n in range(8):
        for k in range(n+1):
            degree=k*(n-k)
            poly=sp.Poly(G(n,k),q)
            L={j:sum(d for d in range(1,k+1) if j%d==0)
                   -sum(d for d in range(n-k+1,n+1) if j%d==0)
               for j in range(1,degree+3)}
            for r in range(degree+3):
                check("base-parameter Bell coefficients n<=7",E(r,L),poly.nth(r))


def bmul(a:dict,b:dict, bound:int) -> dict:
    c={}
    for (i,j),v in a.items():
        for (k,l),w in b.items():
            if i+k<=bound and j+l<=bound:
                ix=(i+k,j+l)
                c[ix]=c.get(ix,ZERO)+v*w
    return {ix:sp.expand(v) for ix,v in c.items() if v!=0}


def bpower(a:dict,n:int,bound:int) -> dict:
    out={(0,0):ONE}
    for _ in range(n):out=bmul(out,a,bound)
    return out


def bslot(a:dict,N:int,base,bound:int) -> dict:
    out={(0,0):ONE}
    for i in range(N):
        fact={ix:base**i*v for ix,v in a.items()}
        fact[(0,0)]=fact.get((0,0),ZERO)+1
        out=bmul(out,fact,bound)
    return out


def shift(a:dict,dx:int,dy:int,bound:int) -> dict:
    return {(i+dx,j+dy):v for (i,j),v in a.items() if i+dx<=bound and j+dy<=bound}


def inversion() -> None:
    """Independent fixed-point series versus the explicit finite formulas."""
    for base in [sp.Rational(1,2),sp.Rational(2)]:
        degree=8
        for N in [1,2,3]:
            phi=[base**(k*(k-1)//2)*G(N,k,base) for k in range(N+1)]
            w=[ZERO]*(degree+1)
            for _ in range(degree+1):
                val=compose(phi,w,degree)
                w=[ZERO]+val[:degree]
            L={j:(-1)**(j-1)*qi(N,base**j) for j in range(1,degree+1)}
            for m in [1,2,3]:
                wm=power(w,m,degree)
                for n in range(m,degree+1):
                    finite=sp.Rational(m,n)*E(n-m,{j:n*v for j,v in L.items()})
                    check("slot Lagrange n<=8,m<=3,N<=3,two bases",wm[n],finite)
        u=[(-1)**n*base**(n*(n-1))/D(n,base) for n in range(degree+1)]
        quotient=mul([base**n*u[n] for n in range(degree+1)],inverse_series(u,degree),degree)
        C=[ONE]+[ZERO]*degree
        for _ in range(degree+1):
            v=mul(C,[base**n*C[n] for n in range(degree+1)],degree)
            C=[ONE]+v[:degree]
        for n in range(degree+1):
            explicit=ZERO
            for k in range(n+1):
                inv=ZERO
                for prof in profiles(n-k):
                    size=sum(m for _,m in prof)
                    inv+=(-1)**size*sp.factorial(size)*sp.prod(u[j]**m/sp.factorial(m) for j,m in prof)
                explicit+=base**k*u[k]*inv
            check("shifted Catalan quotient n<=8,two bases",quotient[n],C[n])
            check("shifted Catalan partition formula n<=8,two bases",explicit,C[n])
        bound=3
        for M,N in [(1,1),(1,2),(2,2),(2,3)]:
            U={};V={}
            for _ in range(2*bound+2):
                Unew=shift(bslot(V,M,base,bound),1,0,bound)
                Vnew=shift(bslot(U,N,base,bound),0,1,bound)
                U,V=Unew,Vnew
            for r,s in [(0,0),(1,0),(0,1),(1,1),(2,1)]:
                H=bmul(bpower(U,r,bound),bpower(V,s,bound),bound)
                for m in range(bound+1):
                    for n in range(bound+1):
                        if n==0:
                            rhs=sp.Integer(s==0 and m==r)
                        elif m==0:
                            rhs=sp.Integer(r==0 and n==s)
                        elif m<r or n<s:
                            rhs=ZERO
                        else:
                            rhs=sp.Rational(m*s+n*r-r*s,m*n)*slot_power(n,N,m-r,base)[m-r]*slot_power(m,M,n-s,base)[n-s]
                        check("coupled inversion m,n<=3,four systems,two bases",H.get((m,n),ZERO),rhs)


def roots() -> None:
    """Symbolic polynomial jets and exact cyclotomic checks."""
    for n in range(9):
        for k in range(n+1):
            poly=G(n,k)
            for d in range(1,7):
                a,b=divmod(n,d);c,r=divmod(k,d)
                diff=poly-sp.binomial(a,c)*G(b,r)
                rem=sp.rem(diff,sp.cyclotomic_poly(d,q),q)
                check("q-Lucas n<=8,orders 1..6",rem,0)
            kap={1:sp.Rational(k*(n-k),2)}
            for j in range(2,6):
                delta=sum(i**j for i in range(1,n+1))-sum(i**j for i in range(1,k+1))-sum(i**j for i in range(1,n-k+1))
                kap[j]=sp.bernoulli(j)*delta/j if j%2==0 else ZERO
            for order in range(6):
                rhs=sp.binomial(n,k)*sum((stirling(order,j,kind=1,signed=True)*bell(j,kap) for j in range(order+1)),ZERO)
                check("derivatives at one n<=8,orders 0..5",sp.diff(poly,q,order).subs(q,1),rhs)
    for zeta,d in [(-ONE,2),(sp.I,4)]:
        for n in range(7):
            for k in range(n+1):
                eps={j:1-int(j<=k)-int(j<=n-k) for j in range(1,n+1)}
                e=n//d-k//d-(n-k)//d
                constant=(-1)**e*sp.prod(sp.Integer(j)**eps[j] if j%d==0 else (1-zeta**j)**eps[j]
                                         for j in range(1,n+1))
                constant=sp.simplify(constant)
                kap={}
                for ell in range(1,5):
                    g=sp.Rational(1,2) if ell==1 else (sp.bernoulli(ell)/ell if ell%2==0 else ZERO)
                    total=ZERO
                    for j in range(1,n+1):
                        if j%d==0:
                            h=g
                        else:
                            a=zeta**j
                            h=-sum((stirling(ell,v,kind=2)*sp.factorial(v-1)*(a/(1-a))**v for v in range(1,ell+1)),ZERO)
                        total+=eps[j]*j**ell*h
                    kap[ell]=sp.simplify(total)
                J={j:(ZERO if j<e else constant*sp.factorial(j)/sp.factorial(j-e)*bell(j-e,kap)) for j in range(5)}
                for order in range(5):
                    rhs=zeta**(-order)*sum((stirling(order,j,kind=1,signed=True)*J[j] for j in range(order+1)),ZERO)
                    check("regularized root jets n<=6,orders 0..4,roots -1 and i",sp.diff(G(n,k),q,order).subs(q,zeta),rhs)
    for base in [sp.Rational(1,2),sp.Rational(2,3),sp.Rational(2)]:
        for N in range(7):
            weights=[(-1)**(N-j)*base**((N-j)*(N-j+1)//2)/(D(j,base)*D(N-j,base)) for j in range(N+1)]
            for ell in range(N+4):
                lhs=sum((weights[j]*base**(j*ell) for j in range(N+1)),ZERO)
                rhs=sp.prod(base**ell-base**r for r in range(1,N+1))/D(N,base)
                check("extrapolation N<=6,three bases,including tail modes",lhs,rhs)
                if ell<=N:
                    check("annihilation moments N<=6,three bases",lhs,int(ell==0))


GROUPS: dict[str, Callable[[], None]] = {
    "algebra":algebra, "coefficients":coefficients, "inversion":inversion, "roots":roots
}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--group",choices=["all",*GROUPS],default="all")
    args=parser.parse_args()
    selected=GROUPS if args.group=="all" else {args.group:GROUPS[args.group]}
    directory=Path(__file__).resolve().parent
    for name,fn in selected.items():
        COUNTS.clear()
        start=time.monotonic()
        fn()
        result={"group":name,"status":"passed","assertions":sum(COUNTS.values()),
                "checks":dict(COUNTS),"seconds":round(time.monotonic()-start,3),
                "python":platform.python_version(),"sympy":sp.__version__,
                "method":"Exact symbolic polynomials and exact rational/algebraic arithmetic; no floating-point comparisons.",
                "scope":"Finite regression tests, not universal formal verification."}
        path=directory/f"verification_{name}.json"
        path.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
        print(f"{name}: {result['assertions']} exact assertions passed ({result['seconds']} s)",flush=True)
    available=[]
    for name in GROUPS:
        path=directory/f"verification_{name}.json"
        if path.exists():available.append(json.loads(path.read_text(encoding="utf-8")))
    if len(available)==len(GROUPS):
        report={"status":"passed","assertions":sum(r["assertions"] for r in available),"groups":available,
                "note":"Each report records a finite exact test range. Proofs are in the article; no Lean formalization is claimed."}
        (directory/"verification_report.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")


if __name__=="__main__":
    main()
