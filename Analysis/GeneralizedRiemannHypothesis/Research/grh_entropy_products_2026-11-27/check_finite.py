#!/usr/bin/env python3
"""Finite checks for the proof, not verification of asymptotic estimates.
Only the Python standard library is used. All counting and TV are exact;
complex Fourier and coefficient comparisons use double precision.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import comb, prod, exp, sqrt, gcd, pi
from cmath import exp as cexp
import json


def primes(n):
    return [p for p in range(2, n+1) if all(p % d for d in range(2, int(sqrt(p))+1))]


def logs(q):
    n=q-1
    for g in range(2,q):
        powers=[pow(g,i,q) for i in range(n)]
        if len(set(powers))==n:
            return {x:i for i,x in enumerate(powers)}
    raise ValueError('requires odd prime modulus')


def product_counts(pool,k,q):
    """DP over subsets, each prime label used at most once."""
    dp=[Counter() for _ in range(k+1)]
    dp[0][1]=1
    for p in pool:
        for j in range(k,0,-1):
            for x,n in dp[j-1].items():
                dp[j][x*p%q]+=n
    assert sum(dp[k].values())==comb(len(pool),k)
    return dp[k]


def tuple_counts(pool,t,q):
    dp=Counter({1:1})
    for _ in range(t):
        nxt=Counter()
        for x,n in dp.items():
            for p in pool:
                nxt[x*p%q]+=n
        dp=nxt
    assert sum(dp.values())==len(pool)**t
    return dp


def pair_moment_count(pool,t,q):
    return sum(n*n for n in tuple_counts(pool,t,q).values())


def fourier(counts,den,characters):
    return [sum(n*chi[g] for g,n in counts.items())/den for chi in characters]


def tv(counts,total,space_size):
    return Fraction(sum(abs(space_size*v-total) for v in counts.values())+
                    (space_size-len(counts))*total,2*total*space_size)


def finite_checks():
    tests=Counter()
    for q in [7,11,13]:
        n=q-1
        pool=[p for p in primes(29) if p!=q]
        log=logs(q)
        chars=[{g:cexp(2j*pi*i*log[g]/n) for g in log} for i in range(n)]
        full_mom={t:pair_moment_count(pool,t,q) for t in [1,2,3]}
        # Exhaust all retained sets of size at least half, and all subset sizes.
        for m in range((len(pool)+1)//2,len(pool)+1):
            for S in combinations(pool,m):
                tests['retained_sets']+=1
                for t in [1,2,3]:
                    exact=pair_moment_count(S,t,q)
                    assert exact<=full_mom[t]
                    mean=[sum(chi[p%q] for p in S)/m for chi in chars]
                    assert abs(sum(abs(x)**(2*t) for x in mean)-n*exact/m**(2*t))<1e-8
                    tests['moment_transfer']+=1
                for k in range(1,m):
                    h=min(k,m-k)
                    C=product_counts(S,k,q)
                    B=comb(m,k)
                    brute=Counter(prod(T)%q for T in combinations(S,k))
                    assert C==brute
                    F=fourier(C,B,chars)
                    Fh=fourier(product_counts(S,h,q),comb(m,h),chars)
                    for i,chi in enumerate(chars):
                        b=abs(sum(chi[p%q] for p in S)/m)
                        u=max(b,sqrt(h/m))
                        assert abs(abs(F[i])-abs(Fh[i]))<1e-8
                        assert abs(F[i]) <= (m+1)*exp(-(1-b)*h/2)+1e-8
                        assert abs(F[i]) <= exp(1.5*h)*u**h+1e-8
                        tests['coefficient_bounds']+=1
                    # All quotients of this cyclic group, not just high-bias quotients.
                    for d in [x for x in range(1,n+1) if n%x==0]:
                        mass=Counter()
                        for g,count in C.items(): mass[log[g]%d]+=count
                        assert sum(mass.values())==B
                        for count in mass.values():
                            assert Fraction(count,B)>=Fraction(1,d*m**(2*(d-1)))
                        # Exact spatial Parseval side. H indexes multiples of n/d.
                        lhs=sum((Fraction(n*C[g]-d*mass[log[g]%d],B))**2 for g in log)/n
                        rhs=sum(abs(F[i])**2 for i in range(n) if i%(n//d))
                        assert abs(float(lhs)-rhs)<1e-8
                        tests['quotient_parseval_mass']+=1
                    tests['subset_count_cases']+=1
    return dict(tests)


def joint_example():
    q=11; n=q-1
    pool=tuple(p for p in primes(37) if p!=q)[:10]
    sizes=[3,3,2]
    def visit(S,ks,prefix=()):
        if not ks:
            yield prefix
            return
        for T in combinations(S,ks[0]):
            rem=tuple(x for x in S if x not in T)
            yield from visit(rem,ks[1:],prefix+(prod(T)%q,))
    C=Counter(visit(pool,sizes)); total=sum(C.values())
    m=len(pool); expected=1; bound=Fraction(0); steps=[]
    for k in sizes:
        expected*=comb(m,k)
        # At this stage the residual set is uniform among m-subsets.
        ds=[tv(product_counts(S,k,q),comb(m,k),n) for S in combinations(pool,m)]
        avg=sum(ds,Fraction(0))/len(ds)
        bound+=avg
        steps.append({'remaining':m,'block':k,'mean_conditional_TV':str(avg)})
        m-=k
    assert total==expected
    joint=tv(C,total,n**len(sizes))
    assert joint<=bound
    return {'modulus':q,'pool':pool,'block_sizes':sizes,'ordered_families':total,
            'reachable_tuples':len(C),'total_target_tuples':n**len(sizes),
            'joint_TV_exact':str(joint),'sum_of_expected_conditional_TV_exact':str(bound),
            'steps':steps}


if __name__=='__main__':
    print(json.dumps({'finite_checks':finite_checks(),'joint_example':joint_example(),
                      'status':'PASS (finite checks only)'},indent=2))
