#!/usr/bin/env python3
"""Exact-arithmetic checks for the Apéry framing supercongruences.

Python 3.10+, standard library only.  Run: python verify.py --out data
Finite checks supplement, and do not replace, the proofs in article.pdf.
"""
from __future__ import annotations

import argparse
import csv
import json
import math
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
from typing import Sequence


def primes_up_to(n: int) -> list[int]:
    return [p for p in range(2, n + 1)
            if all(p % d for d in range(2, math.isqrt(p) + 1))]


def valuation(n: int, p: int) -> int:
    """Valuation of a nonzero integer; callers handle zero separately."""
    if n == 0:
        raise ValueError("valuation(0) is infinite")
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def divides_power(n: int, p: int, e: int) -> bool:
    return n % (p ** e) == 0


def apery_binomial(n: int) -> int:
    return sum(math.comb(n, k) ** 2 * math.comb(n + k, k) ** 2
               for k in range(n + 1))


def apery_recurrence(limit: int) -> list[int]:
    a = [1]
    if limit == 0:
        return a
    a.append(5)
    for n in range(1, limit):
        num = (2*n + 1)*(17*n*n + 17*n + 5)*a[n] - n**3*a[n-1]
        den = (n+1)**3
        assert num % den == 0
        a.append(num // den)
    return a


class ExactFamily:
    def __init__(self, a: Sequence[int]):
        self.a = tuple(a)

    @lru_cache(maxsize=None)
    def coefficient(self, exponent: int, degree: int) -> int:
        """[z^degree] G(z)^exponent, by logarithmic differentiation."""
        if degree < 0 or degree >= len(self.a):
            raise ValueError("degree outside the precomputed Apéry range")
        h = [1]
        for j in range(1, degree + 1):
            num = exponent * sum(self.a[k]*h[j-k] for k in range(1, j+1))
            assert num % j == 0, (exponent, degree, j)
            h.append(num // j)
        return h[degree]

    @lru_cache(maxsize=None)
    def normalized(self, t: int, n: int) -> int:
        if n < 1:
            raise ValueError("the normalized family is defined here for n >= 1")
        if t == 0:
            return self.a[n]
        c = self.coefficient(t*n, n)
        assert c % t == 0, (t, n)
        return c // t

    def u(self, m: int, n: int) -> int:
        return self.coefficient(m*n, n)

    def v(self, m: int, n: int) -> int:
        # The independent small-degree checks below do not use this identity.
        return m*self.normalized(m-1, n)


# Truncated formal power-series operations over Q; independent of ExactFamily.
def trim(a: Sequence[Q | int], N: int) -> list[Q]:
    return [Q(a[i]) if i < len(a) else Q(0) for i in range(N+1)]


def add(a: Sequence[Q], b: Sequence[Q], N: int) -> list[Q]:
    return [x+y for x,y in zip(trim(a,N),trim(b,N))]


def scale(a: Sequence[Q], c: Q | int, N: int) -> list[Q]:
    return [Q(c)*x for x in trim(a,N)]


def mul(a: Sequence[Q], b: Sequence[Q], N: int) -> list[Q]:
    a,b = trim(a,N),trim(b,N)
    out = [Q(0)]*(N+1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b[:N+1-i]):
                if y:
                    out[i+j] += x*y
    return out


def inv(a: Sequence[Q], N: int) -> list[Q]:
    a = trim(a,N)
    if not a[0]:
        raise ValueError("series is not a unit")
    b = [1/a[0]]
    for n in range(1,N+1):
        b.append(-sum(a[k]*b[n-k] for k in range(1,n+1))/a[0])
    return b


def power(a: Sequence[Q], k: int, N: int) -> list[Q]:
    if k < 0:
        return power(inv(a,N), -k, N)
    result = trim([1],N)
    base = trim(a,N)
    while k:
        if k & 1:
            result = mul(result,base,N)
        k //= 2
        if k:
            base = mul(base,base,N)
    return result


def compose(a: Sequence[Q], b: Sequence[Q], N: int) -> list[Q]:
    a,b = trim(a,N),trim(b,N)
    if b[0]:
        raise ValueError("inner series must have zero constant coefficient")
    out = trim([0],N)
    for c in reversed(a):
        out = mul(out,b,N)
        out[0] += c
    return out


def reversion(a: Sequence[Q], N: int) -> list[Q]:
    """Triangular compositional inversion; intentionally independent of Lagrange."""
    a = trim(a,N)
    if a[0] != 0 or a[1] != 1:
        raise ValueError("expected z + O(z^2)")
    b = trim([0,1],N)
    for n in range(2,N+1):
        b[n] = -compose(a,b,n)[n]
    assert compose(a,b,N) == trim([0,1],N)
    return b


def logarithm(a: Sequence[Q], N: int) -> list[Q]:
    a = trim(a,N)
    if a[0] != 1:
        raise ValueError("logarithm requires constant coefficient 1")
    deriv = [Q(k+1)*a[k+1] for k in range(N)]
    q = mul(deriv,inv(a,N),N)
    return [Q(0)] + [q[k-1]/k for k in range(1,N+1)]


def delta(a: Sequence[Q], N: int) -> list[Q]:
    return [k*x for k,x in enumerate(trim(a,N))]


def frobenius(a: Sequence[Q], p: int, N: int) -> list[Q]:
    a=trim(a,N)
    return [a[k//p] if k%p == 0 else Q(0) for k in range(N+1)]


def defect(a: Sequence[Q], p: int, N: int) -> list[Q]:
    return add(scale(frobenius(a,p,N),Q(1,p*p),N),scale(a,-1,N),N)


def local_integral(q: Q, p: int, allowance: int = 0) -> bool:
    return q.denominator % p != 0 or (p**allowance*q).denominator % p != 0


def independent_formal_checks(fam: ExactFamily, N: int = 14) -> dict[str,int]:
    G = [Q(fam.coefficient(1,n)) for n in range(N+2)]
    zG = [Q(0)] + G[:N+1]
    psi = reversion(zG,N+1)
    F = inv(psi[1:],N)
    assert all(x.denominator == 1 for x in F)
    assert compose(G,psi,N) == F
    # Independently compute powers of the reverted F by rational convolution.
    count = 0
    for m in range(-4,5):
        for n in range(1,N+1):
            direct = power(F,m*n,n)[n]
            assert direct == fam.v(m,n), (m,n)
            count += 1
    W = [Q(0)]+[Q(fam.a[n],n*n) for n in range(1,N+1)]
    L = delta(W,N)
    identity_count = 0
    for t in [-3,-1,0,1,2,4]:
        f = trim([Q(0)]+power(G,-t,N),N)
        x = reversion(f,N)
        l = compose(L,x,N)
        Wt = add(compose(W,x,N),scale(mul(l,l,N),Q(-t,2),N),N)
        assert Wt == [Q(0)]+[Q(fam.normalized(t,n),n*n)
                              for n in range(1,N+1)]
        for p in [2,3,5]:
            R = defect(W,p,N)
            D = delta(R,N)
            unit = compose(G,x,N)
            # S = log(B(w^p))/p - log(B(w)).
            logunit = logarithm(unit,N)
            S = add(scale(frobenius(logunit,p,N),Q(1,p),N),
                    scale(logunit,-1,N),N)
            assert all(local_integral(q,p) for q in S)
            rhs = compose(R,x,N)
            rhs = add(rhs,scale(mul(S,compose(D,x,N),N),t,N),N)
            rhs = add(rhs,scale(mul(S,S,N),Q(-t,2),N),N)
            xpower = power(x,p,N)
            derivative = delta(W,N)
            spower = S
            for k in range(2,N+1):
                derivative = delta(derivative,N)
                spower = mul(spower,S,N)
                term = mul(spower,compose(derivative,xpower,N),N)
                c = Q(p**(k-2)*t**k,math.factorial(k))
                rhs = add(rhs,scale(term,c,N),N)
            lhs = defect(Wt,p,N)
            assert lhs == rhs, (t,p)
            allowance = int(p == 2 and t%2 != 0)
            assert all(local_integral(q,p,allowance) for q in lhs)
            identity_count += 1
    return {"independent_reversion_power_checks":count,
            "exact_frobenius_defect_identity_checks":identity_count,
            "formal_series_degree":N}


def main() -> None:
    if not __debug__:
        raise RuntimeError("Run without -O: verification assertions must be enabled")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',type=Path,default=Path('data'))
    parser.add_argument('--limit',type=int,default=150)
    args=parser.parse_args()
    if args.limit < 125:
        parser.error('--limit must be at least 125 to include the advertised checks')
    args.out.mkdir(parents=True,exist_ok=True)
    limit=args.limit
    a=apery_recurrence(limit)
    for n in range(limit+1):
        assert a[n] == apery_binomial(n),n
    fam=ExactFamily(a)
    seed_checks=0
    for p in primes_up_to(limit):
        for N in range(p,limit+1,p):
            assert divides_power(a[N]-a[N//p],p,2*valuation(N,p))
            seed_checks += 1
    # Parameters include negative values, 0, and multiples of each small prime.
    parameters=list(range(-10,11))
    primes=[3,5,7,11,13]
    rows=[]
    odd_checks=0
    for t in parameters:
        for p in primes:
            for r in range(1,5):
                for n in range(1,5):
                    N=n*p**r
                    if N>limit:
                        continue
                    d=fam.normalized(t,N)-fam.normalized(t,N//p)
                    e=2*valuation(N,p)
                    assert divides_power(d,p,e),(t,p,r,n)
                    rows.append([t,p,r,n,N,e,
                                 'infinity' if not d else valuation(d,p),
                                 str(d//p**e)])
                    odd_checks += 1
    two_checks=0
    u_parameter_checks=0
    u_two_parameter_checks=0
    v_all_prime_checks=0
    for m in parameters:
        for N in range(2,limit+1,2):
            r=valuation(N,2)
            d=fam.normalized(m,N)-fam.normalized(m,N//2)
            e=2*r if m%2 == 0 else 2*r-1
            assert divides_power(d,2,e),(m,N)
            two_checks += 1
            ud=fam.u(m,N)-fam.u(m,N//2)
            ue=2*r+valuation(m,2) if m and m%2 == 0 else 2*r-1
            assert divides_power(ud,2,ue),(m,N,'u_2')
            u_two_parameter_checks += 1
            vd=fam.v(m,N)-fam.v(m,N//2)
            ve=2*r+valuation(m,2)-1 if m and m%2 == 0 else 2*r
            assert divides_power(vd,2,ve),(m,N,'v_2')
            v_all_prime_checks += 1
        for p in primes:
            for N in range(p,min(limit,50)+1,p):
                e=2*valuation(N,p)
                ud=fam.u(m,N)-fam.u(m,N//p)
                vd=fam.v(m,N)-fam.v(m,N//p)
                extra=valuation(m,p) if m else 0
                assert divides_power(ud,p,e+extra),(m,p,N,'u')
                assert divides_power(vd,p,e+extra),(m,p,N,'v')
                u_parameter_checks += 1
                v_all_prime_checks += 1
    independent=independent_formal_checks(fam)
    # Exact counterexamples to two tempting overstatements.
    d=fam.u(1,7)-fam.u(1,1)
    assert d == 5082313271 and d%49 == 0 and d%343 == 294
    assert fam.u(1,2)-fam.u(1,1) == 118
    counterexamples={
       "cubic_precision_u": {"m":1,"p":7,"n":1,"r":1,
          "difference":str(d),"valuation":valuation(d,7),"residue_mod_343":d%343},
       "cubic_precision_v": {"m":2,"p":7,"n":1,"r":1,
          "difference":str(2*d),"valuation":valuation(2*d,7),"residue_mod_343":(2*d)%343},
       "unrestricted_prime_2_u": {"m":1,"N":2,"difference":118,
          "residue_mod_4":2}}
    with (args.out/'odd_prime_checks.csv').open('w',newline='') as f:
        w=csv.writer(f)
        w.writerow(['t','p','r','n','N','proved_exponent','actual_valuation','scaled_difference'])
        w.writerows(rows)
    with (args.out/'sample_coefficients.csv').open('w',newline='') as f:
        w=csv.writer(f)
        w.writerow(['n','apery_a_n','G_coefficient','B_minus_2','B_minus_1','B_0',
                    'B_1','B_2','u_1','v_1','v_2'])
        for n in range(1,21):
            w.writerow([n,a[n],fam.coefficient(1,n),
                        *[fam.normalized(t,n) for t in [-2,-1,0,1,2]],
                        fam.u(1,n),fam.v(1,n),fam.v(2,n)])
    summary={"status":"all checks passed", "arithmetic":"exact integers and fractions",
       "apery_binomial_vs_recurrence_indices":[0,limit],
       "apery_seed_congruence_checks":seed_checks,
       "framing_parameters":parameters,"odd_primes":primes,
       "odd_prime_normalized_congruence_checks":odd_checks,
       "prime_2_normalized_bound_checks":two_checks,
       "odd_prime_parameter_sensitive_u_checks":u_parameter_checks,
       "prime_2_parameter_sensitive_u_checks":u_two_parameter_checks,
       "all_prime_v_checks":v_all_prime_checks, **independent,
       "counterexamples":counterexamples,
       "disclaimer":"Finite exact computations are not a proof for all indices; see article.pdf."}
    (args.out/'verification_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))


if __name__ == '__main__':
    main()
