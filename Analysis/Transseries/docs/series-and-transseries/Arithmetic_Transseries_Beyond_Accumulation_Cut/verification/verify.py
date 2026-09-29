#!/usr/bin/env python3
"""Reproduce the finite exact audits and high-precision diagnostics.

Requirements: Python >=3.10 and mpmath. No network access is used.
These computations are not a proof assistant or outward-rounded intervals.
The general theorems are proved in the accompanying article.
"""
from __future__ import annotations
import csv
import json
import math
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
import mpmath as mp

OUT = Path(__file__).resolve().parent

def divisors(n: int) -> list[int]:
    if n < 1:
        raise ValueError('n must be positive')
    lo, hi = [], []
    for d in range(1, math.isqrt(n) + 1):
        if n % d == 0:
            lo.append(d)
            if d*d != n:
                hi.append(n//d)
    return lo + hi[::-1]

def phi(n: int) -> int:
    if n < 1:
        raise ValueError('n must be positive')
    ans, rest, p = n, n, 2
    while p*p <= rest:
        if rest % p == 0:
            ans -= ans//p
            while rest % p == 0:
                rest //= p
        p += 1
    if rest > 1:
        ans -= ans//rest
    return ans

def mobius(n: int) -> int:
    if n < 1:
        raise ValueError('n must be positive')
    ans, rest, p = 1, n, 2
    while p*p <= rest:
        if rest % p == 0:
            rest //= p
            ans = -ans
            if rest % p == 0:
                return 0
        p += 1
    return -ans if rest > 1 else ans

def mul(a, b, size):
    ans = [a[0]*0 for _ in range(size)]
    for i in range(min(len(a), size)):
        for j in range(min(len(b), size-i)):
            ans[i+j] += a[i]*b[j]
    return ans

def reciprocal(a, size):
    if not a[0]:
        raise ZeroDivisionError('zero constant jet coefficient')
    ans = [a[0]*0 for _ in range(size)]
    ans[0] = 1/a[0]
    for k in range(1, size):
        ans[k] = -sum(a[j]*ans[k-j] for j in range(1,min(k+1,len(a))))/a[0]
    return ans

def power(a, exponent, size):
    ans = [a[0]*0 for _ in range(size)]
    ans[0] = a[0]*0+1
    for _ in range(exponent):
        ans = mul(ans,a,size)
    return ans

def compose(a, inner, size):
    # inner has zero constant coefficient in the exact audits below.
    ans = [inner[0]*0 for _ in range(size)]
    for c in a[::-1]:
        ans = mul(ans,inner,size)
        ans[0] += c
    return ans

def inverse_jet(a, X, actions_weights, M):
    """Return δ_m from the homogeneous Lagrange formula, 1<=m<=M.
    actions_weights contains (lambda, c*exp(-lambda*X)), already evaluated.
    All inputs may be Fraction or mpmath numbers.
    """
    if not isinstance(M, int) or M < 1:
        raise ValueError("M must be a positive integer")
    if not X:
        raise ValueError("X must be nonzero")
    zero = a*0
    E = [sum((weight*(-lam)**k/math.factorial(k)
              for lam,weight in actions_weights),zero) for k in range(M)]
    # J_X(u)=(1-(1+u/X)exp(-a*u))/u.
    J = [-((-a)**(k+1)/math.factorial(k+1)
           +(-a)**k/(X*math.factorial(k))) for k in range(M)]
    F = mul(E,reciprocal(J,M),M)
    terms = []
    Fm = [zero+1]+[zero]*(M-1)
    for m in range(1,M+1):
        Fm = mul(Fm,F,M)
        terms.append((-1)**m*Fm[m-1]/m)
    return terms

def action_tuples(r: Q, m: int, lower: int=2):
    """Sorted tuples d_i>=2 with sum(1-1/d_i)=r. Finite exact search."""
    target = Q(m)-r
    def egyptian(t: Q, k: int, low: int):
        if k == 0:
            if t == 0:
                yield ()
            return
        if t <= 0:
            return
        if k == 1:
            if t.numerator == 1 and t.denominator >= low:
                yield (t.denominator,)
            return
        for d in range(max(low, math.ceil(1/t)), math.floor(Q(k)/t)+1):
            for tail in egyptian(t-Q(1,d),k-1,d):
                yield (d,)+tail
    yield from egyptian(target,m,lower)

def exact_audits():
    checks = 0
    # Finite divisor-zeta map diagonalizes lcm convolution.
    for N in (8,17,30):
        f = {i: Q((i*i+3*i)%11-5, i+1) for i in range(1,N+1)}
        g = {i: Q((7*i+1)%13-6, i+2) for i in range(1,N+1)}
        conv = defaultdict(Q)
        for i in f:
            for j in g:
                conv[math.lcm(i,j)] += f[i]*g[j]
        for n in range(1,3*N+1):
            ds = divisors(n)
            assert sum(conv[d] for d in ds) == sum(f.get(d,0) for d in ds)*sum(g.get(d,0) for d in ds)
            checks += 1
    for n in range(1,301):
        assert sum(phi(d) for d in divisors(n)) == n
        assert sum(mobius(d) for d in divisors(n)) == (1 if n==1 else 0)
        checks += 2
    # Substitution into the exact transformed equation u J_X(u)+z E(X+u)=0.
    # Here exponential amplitudes are independent rational formal inputs.
    M = 7
    for X in (Q(5),Q(11),Q(25,2)):
        a = Q(1)
        aw = [(Q(1,2),Q(2,7)),(Q(2,3),Q(-3,11)),(Q(5,6),Q(5,13))]
        terms = inverse_jet(a,X,aw,M)
        delta = [Q(0)]+terms
        size=M+1
        J = [-((-a)**(k+1)/math.factorial(k+1)+(-a)**k/(X*math.factorial(k))) for k in range(size)]
        EJ = [sum(w*(-l)**k/math.factorial(k) for l,w in aw) for k in range(size)]
        residual = mul(delta,compose(J,delta,size),size)
        Ecomp=compose(EJ,delta,size)
        for k in range(1,size):
            residual[k] += Ecomp[k-1]
        assert all(c==0 for c in residual)
        checks += size
    # Universal resonance derivative for m=2,...,14 and all 1<=k<m.
    # Differentiating binom(r,m) at its integer root k gives the product below.
    for m in range(2,15):
        for k in range(1,m):
            deriv=Q(math.prod(k-j for j in range(m) if j!=k),math.factorial(m))
            expected=Q((-1)**(m-1-k),m*math.comb(m-1,k))
            assert deriv==expected
            checks += 1
    # The two exact inverse coefficient coordinates agree over Q.
    # J-coordinate in u versus logarithmic v=1+w coordinate, at finite X.
    for X in (Q(5),Q(11)):
        for m in range(1,9):
            for alpha in (Q(1),Q(4,3),Q(3,2),Q(2),Q(17,6)):
                size=m
                J=[-((-Q(1))**(k+1)/math.factorial(k+1)
                     +(-Q(1))**k/(X*math.factorial(k))) for k in range(size)]
                jinv=power(reciprocal(J,size),m,size)
                expo=[(-alpha)**k/math.factorial(k) for k in range(size)]
                left=Q((-1)**m,m)*mul(expo,jinv,size)[m-1]
                # B(w)=(1+w)log(1+w)/w; B_0=1,
                # B_j=(-1)^(j+1)/(j*(j+1)) for j>=1.
                B=[Q(1)]+[Q((-1)**(j+1),j*(j+1)) for j in range(1,size)]
                K=[-v/X for v in B];K[0]+=1
                rhsjet=power(reciprocal(K,size),m,size)
                binom=[Q(1)]
                for k in range(1,size):
                    binom.append(binom[-1]*(alpha-k)/k)
                right=-Q(1,m)*mul(binom,rhsjet,size)[m-1]
                assert left==right
                checks+=1
    expected={
        (Q(1),2):[(2,2)],
        (Q(4,3),2):[(2,6),(3,3)],
        (Q(3,2),2):[(3,6),(4,4)],
        (Q(3,2),3):[(2,2,2)],
    }
    for key, tuples in expected.items():
        assert list(action_tuples(*key))==tuples
        checks += 1
    return {'passed_exact_assertions':checks,
            'formal_inverse_residual_order':M,
            'arithmetic_identity_max_n':300,
            'resonance_derivative_max_m':14,
            'action_collision_tests':4, 'finite_X_coordinate_checks':80}

def numerical_audits():
    mp.mp.dps = 400
    records=[]
    resonance_records=[]
    for kind,weight_fn in [('necklace',phi),('primitive',mobius)]:
        for q,n in [(2,20),(2,30),(2,60),(2,120),(3,60),(3,210)]:
            a=mp.log(q)
            ds=[d for d in divisors(n) if d>=2]
            # Exact integer enumeration, not a floating forward approximation.
            numerator=sum(weight_fn(d)*q**(n//d) for d in divisors(n))
            assert numerator % n == 0
            y=mp.mpf(numerator//n)
            X=-mp.lambertw(-a/y,-1)/a
            aw=[(a*(1-mp.mpf(1)/d),mp.mpf(weight_fn(d))*mp.exp(-a*(1-mp.mpf(1)/d)*X)) for d in ds]
            terms=inverse_jet(a,X,aw,4)
            truth=mp.mpf(n)-X
            A=sum(abs(w) for _,w in aw)
            r=1/(8*a)
            theta=2*mp.exp(a*r)*A/(a*r)
            assert X>=4/a and theta<1
            partial=mp.mpf('0')
            for m,t in enumerate(terms,1):
                partial +=t
                err=abs(truth-partial)
                bound=r*theta**(m+1)/((m+1)*(1-theta))
                assert err <= bound
                records.append(dict(kind=kind,q=q,n=n,M=m,
                    abs_error=mp.nstr(err,12),cauchy_bound=mp.nstr(bound,12),
                    error_bound_ratio=mp.nstr(err/bound,8),theta=mp.nstr(theta,10)))
            E=sum(w for _,w in aw)
            p=a-1/X
            first=-a*mp.exp(-a*X)/(2*X*p**3)
            ratio=(truth+E/p)/first
            resonance_records.append(dict(kind=kind,q=q,n=n,
                first_post_accumulation_ratio=mp.nstr(ratio,18)))
    return records,resonance_records

def main():
    exact=exact_audits()
    rows,resonance=numerical_audits()
    with (OUT/'inverse_error_checks.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=rows[0].keys());writer.writeheader();writer.writerows(rows)
    with (OUT/'resonance_checks.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=resonance[0].keys());writer.writeheader();writer.writerows(resonance)
    report={'status':'all checks passed','exact':exact,'working_decimal_digits':400,
            'numerical_error_bound_checks':len(rows),'post_accumulation_checks':resonance,
            'qualification':'Finite exact audits and non-interval high-precision diagnostics, not general formal verification.'}
    (OUT/'results.json').write_text(json.dumps(report,indent=2)+'\n')
    # Small table consumed by the article. Generated values, not manually typed.
    selected=[r for r in rows if r['kind']=='necklace' and r['q']==2 and r['n'] in (20,60,120) and r['M'] in (1,2,4)]
    def texnum(s):
        v=mp.mpf(s)
        if not v: return '0'
        e=int(mp.floor(mp.log10(abs(v)))); mant=v/mp.power(10,e)
        return mp.nstr(mant,4)+r'\times10^{'+str(e)+'}'
    with (OUT/'table.tex').open('w') as f:
        for r in selected:
            f.write(f"{r['n']} & {r['M']} & ${texnum(r['abs_error'])}$ & ${texnum(r['cauchy_bound'])}$ \\\\\n")
    print(json.dumps({k:v for k,v in report.items() if k!='post_accumulation_checks'},indent=2))
    print('Post-accumulation ratios:')
    for r in resonance: print(r)

if __name__=='__main__':
    main()
