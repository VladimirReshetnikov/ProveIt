#!/usr/bin/env python3
"""Exact finite checks for the finite-jet pressure article (standard library only).
These checks do not establish the analytic limit theorems.
ed. (2026-09-30): the record goes to data/rerun/verification.json unless
--output is given (the recorded data/verification.json is not overwritten by
default), and it is written with LF line endings on every platform.
"""
from __future__ import annotations
import argparse, itertools, json, math, random
from fractions import Fraction as Q
from pathlib import Path


def mul(a, b, n):
    out = [Q(0)] * (n+1)
    for i, v in enumerate(a[:n+1]):
        if v:
            for j, w in enumerate(b[:n+1-i]):
                if w: out[i+j] += v*w
    return out


def compose(a, b, n):
    out = [Q(0)]*(n+1)
    for c in reversed(a[:n+1]):
        out = mul(out, b, n)
        out[0] += c
    return out


def powers(a, n):
    p = [Q(1)] + [Q(0)]*n
    for _ in range(n+1):
        yield p
        p = mul(p, a, n)


def rising(a, r):
    out=Q(1)
    for j in range(r): out *= a+j
    return out


def pressure_coefficients(s, theta, a, n):
    """p[k] = [t^k] Psi_(s*k)( t A'/(1-theta*A) ) / k."""
    A = [Q(0)] + [Q(v) for v in a[:n]]
    A += [Q(0)]*(n+1-len(A))
    reciprocal = [Q(1)] + [Q(0)]*n
    for k in range(1,n+1):
        reciprocal[k] = theta*sum(A[j]*reciprocal[k-j] for j in range(1,k+1))
    B = mul([k*A[k] for k in range(n+1)], reciprocal, n)
    bp=list(powers(B,n))
    p=[Q(0)]*(n+1)
    for k in range(1,n+1):
        p[k]=sum(rising(s*k,r-1)*bp[r][k]/math.factorial(r) for r in range(1,k+1))/k
    return p


def pressure_by_implicit(s, theta, a, n):
    A=[Q(0)]+[Q(v) for v in a[:n]]
    A += [Q(0)]*(n+1-len(A))
    rec=[Q(1)]+[Q(0)]*n
    for k in range(1,n+1): rec[k]=theta*sum(A[j]*rec[k-j] for j in range(1,k+1))
    B=mul([k*A[k] for k in range(n+1)],rec,n)
    y=[Q(0),Q(1)]+[Q(0)]*(n-1)
    for _ in range(n+1):
        d=compose(B,y,n)
        phi=[Q(0)]*(n+1)
        for r,p in enumerate(powers(d,n)):
            c=rising(s,r)/math.factorial(r)
            for k in range(n+1): phi[k]+=c*p[k]
        y=[Q(0)]+phi[:n]
    Ay=compose(A,y,n); d=compose(B,y,n)
    P=[Q(0)]*(n+1)
    for r,p in enumerate(powers(Ay,n)):
        if r:
            c=theta**(r-1)/r
            for k in range(n+1): P[k]+=c*p[k]
    for r,p in enumerate(powers(d,n)):
        if r>=2:
            for k in range(n+1): P[k]-=s*p[k]/r
    # independent envelope identity x P'(x) = B(y(x))
    assert [k*P[k] for k in range(n+1)] == d
    return P


def coefficients_from_recurrence(weights, C, theta, order):
    """Return coefficients g[0:order+1] of f_theta's compositional inverse."""
    g=[Q(0),Q(1)]+[Q(0)]*(order-1)
    for n in range(2,order+1):
        b=[Q(1)]+[Q(0)]*(n-1)
        for k in range(1,n):
            b[k]=C*sum((n*j+theta*(k-j))*weights[j]*b[k-j] for j in range(1,k+1))/k
        g[n]=b[n-1]/n
    return g


def forward(weights,C,theta,n):
    W=[Q(0)]+[C*w for w in weights[1:n]]
    W += [Q(0)]*(n+1-len(W))
    phi=[Q(0)]*(n+1)
    factor=Q(1)
    for r,p in enumerate(powers(W,n)):
        if r:
            factor *= -(1-theta*(r-1))/r
        for k in range(n+1): phi[k]+=factor*p[k]
    return [Q(0)]+phi[:n]


def compositions(m):
    if m==0:
        yield ()
    else:
        for j in range(1,m+1):
            for tail in compositions(m-j): yield (j,)+tail


def product(values):
    result=Q(1)
    for v in values: result*=v
    return result


def localized_grouped(n,h,w,C,theta):
    def rec(j,remaining,counts):
        if j>h:
            d=sum(i*c for i,c in enumerate(counts))
            ell=sum(counts)
            yield product(n+theta*r for r in range(1,ell+1))*C**ell*w[n-1-d]/w[n-1]*product(w[i]**c/Q(math.factorial(c)) for i,c in enumerate(counts) if i)
        else:
            for c in range(remaining//j+1):
                yield from rec(j+1,remaining-j*c,counts+[c])
    return sum(rec(1,h,[0]),Q(0))


def main():
    parser=argparse.ArgumentParser()
    # ed. (2026-09-30): the default leaves the recorded data/verification.json untouched.
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'data'/'rerun'/'verification.json',
                        help='JSON output file (default: data/rerun/verification.json; '
                             'pass data/verification.json to overwrite the recorded file)')
    args=parser.parse_args()
    checks=0
    # Exact inverse identities for both classical endpoints and interpolation.
    order=18
    for theta in (Q(-1),Q(-1,2),Q(0),Q(1),Q(3,2),Q(3)):
        for C in (Q(1),Q(2,3)):
            w=[Q(1)]+[Q(math.factorial(j)) for j in range(1,order+1)]
            w[2]=Q(7,3);w[4]=Q(17,5)
            g=coefficients_from_recurrence(w,C,theta,order)
            f=forward(w,C,theta,order)
            identity=[Q(0),Q(1)]+[Q(0)]*(order-1)
            assert compose(f,g,order)==identity
            assert compose(g,f,order)==identity
            checks+=2*(order+1)
    # Ordered compositions versus grouped one-large-part terms.
    for theta in (Q(-1),Q(0),Q(1),Q(2)):
        for n in range(5,13):
            w=[Q(1)]+[Q(j*j+1,j+1) for j in range(1,n)]
            C=Q(3,2);h=(n-2)//2
            direct=Q(0)
            total=Q(0)
            for parts in compositions(n-1):
                k=len(parts)
                val=product(n+theta*r for r in range(k))*C**k*product(w[j] for j in parts)/(n*C*w[n-1]*math.factorial(k))
                total+=val
                if max(parts)>=n-1-h: direct+=val
            assert direct==localized_grouped(n,h,w,C,theta)
            gn=coefficients_from_recurrence(w,C,theta,n)[n]
            assert total==gn/(C*w[n-1])
            checks+=2
    # All pressure formulas agree over rational inputs through order seven.
    rng=random.Random(20260930)
    degree=7
    for s in (Q(1,2),Q(1,3),Q(1,4),Q(2,5),Q(3,2)):
        for theta in (Q(-1),Q(0),Q(1),Q(3,2)):
            a=[Q(rng.randint(1,7),rng.randint(1,5)) for _ in range(degree)]
            p=pressure_coefficients(s,theta,a,degree)
            assert p==pressure_by_implicit(s,theta,a,degree)
            checks+=degree+1
            a1,a2,a3,a4=a[:4]
            printed=[
                a1,
                a2+(s+theta)*a1*a1/2,
                a3+(2*s+theta)*a1*a2+
                    (s*s/2+s*theta+s/6+theta*theta/3)*a1**3,
                a4+(3*s+theta)*a1*a3+(2*s+theta/2)*a2*a2+
                    (4*s*s+5*s*theta+s+theta*theta)*a1*a1*a2+
                    (2*s**3/3+2*s*s*theta+s*s/2+3*s*theta*theta/2+
                     s*theta/2+s/12+theta**3/4)*a1**4]
            assert p[1:5]==printed
            checks+=4
    # Exact critical coefficient of a1^k: ((theta+1)^k-theta^k)/k^2.
    for k in range(1,11):
        for theta in (Q(-1),Q(-1,2),Q(0),Q(1),Q(2)):
            p=pressure_coefficients(Q(1,k),theta,[Q(1)]+[Q(0)]*(k-1),k)
            assert p[k]==((theta+1)**k-theta**k)/k**2
            checks+=1
    # 256 sign patterns: the saturating negative forward series dominates.
    degree=9;w=[Q(1)]+[Q(math.factorial(j)) for j in range(1,degree)]
    bound=coefficients_from_recurrence(w,Q(1),Q(1),degree)[degree]
    for signs in itertools.product((-1,1),repeat=degree-1):
        a=[Q(0)]+[signs[j-1]*w[j] for j in range(1,degree)]
        # Lagrange power (1+sum a_j z^j)^(-degree).
        b=[Q(1)]+[Q(0)]*(degree-1)
        for k in range(1,degree):
            b[k]=-sum((degree*j+k-j)*a[j]*b[k-j] for j in range(1,k+1))/k
        assert abs(b[degree-1]/degree)<=bound
        checks+=1
    record={'status':'passed','arithmetic':'exact fractions and integers','scalar_checks':checks,
      'inverse_order':order,'pressure_order':7,'pressure_cases':20,
      'extremizer_sign_patterns':256,'critical_pure_a1_cases':50,
      'scope':'Finite algebraic checks only; no proof-assistant certification or proof of the asymptotic limits.'}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    # ed. (2026-09-30): newline='\n' so the JSON is LF on Windows too.
    args.output.write_text(json.dumps(record,indent=2)+'\n',newline='\n')
    print(json.dumps(record,indent=2))

if __name__=='__main__': main()
