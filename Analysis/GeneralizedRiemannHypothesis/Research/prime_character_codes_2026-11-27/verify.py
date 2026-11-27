#!/usr/bin/env python3
"""Exact finite checks for the prime-character-code research note.
No external libraries; no assertion here substitutes for the analytic proof.
"""
from fractions import Fraction as F
from itertools import combinations
from math import isqrt, gcd
import json


def check_constants(max_s=10000):
    for s in range(2, max_s+1):
        eta, eps, tau = F(1,1000*s**3), F(1,100*s**2), F(1,100*s)
        a = (s-1)*eta + tau*tau
        assert a <= F(1,500*s*s)
        assert s*(1-a) > (s-1)*(1+eps)
        assert s*(eps+a) <= F(1,80*s)
        assert F(1,80*s) <= F(1,8)
        lhs = (1+F(1,s))*(1-F(1,500*s*s))*(1-F(1,20*s))**2
        assert lhs >= (1+F(1,s))*(1-F(1,9*s))
        assert (1+F(1,s))*(1-F(1,9*s)) >= 1+F(5,6*s)
        assert 1+F(5,6*s) > 1+s*eta
        assert 2*(1-(s-1)*eta) > 1+eps
        assert (s-1)*eta <= eps
        assert (1-a)/s > 0
    return max_s-1


def walsh(x,a):
    return (-1)**((x&a).bit_count() % 2)


def rank(M):
    """Rank over Q, using integer row operations + gcd normalization."""
    if not M:
        return 0
    M = [list(row) for row in M]
    nr, nc = len(M), len(M[0]); r = 0
    for j in range(nc):
        k = next((i for i in range(r,nr) if M[i][j]),None)
        if k is None:
            continue
        M[r], M[k] = M[k], M[r]
        pivot = M[r][j]
        for i in range(r+1,nr):
            if M[i][j]:
                u = M[i][j]
                M[i] = [pivot*M[i][h]-u*M[r][h] for h in range(nc)]
                d = gcd(*M[i])
                if d>1: M[i] = [z//d for z in M[i]]
        r += 1
        if r == nr: break
    return r


def is_subgroup(H):
    H=set(H)
    return 0 in H and all(a^b in H for a in H for b in H)


def subgroup_cosets(n,s):
    G=range(n)
    ans=set()
    for H in combinations(G,s):
        if not is_subgroup(H): continue
        K=[x for x in G if all(walsh(x,h)==1 for h in H)]
        for g in G: ans.add(tuple(sorted(g^x for x in K)))
    return ans


def exact_minimum(weights,s):
    """Min sample weight of a nonzero vector with <=s Walsh frequencies.
    A nonzero coefficient vector supported inside A vanishes outside U iff
    the corresponding complement-row matrix has rank < len(A).
    Since a smaller support can be padded, enumerate |A|=s.  All weights
    positive, so minimum witnesses have actual point-support exactly U.
    """
    n=len(weights); G=tuple(range(n)); Ulist=[]
    for k in range(1,n+1):
        for U in combinations(G,k):
            Ulist.append((sum(weights[x] for x in U),U))
    Ulist.sort()
    answer=None; patterns=set(); pair_count=0; rigid=True
    As=list(combinations(G,s))
    for weight,U in Ulist:
        if answer is not None and weight>answer: break
        outside=[x for x in G if x not in U]
        for A in As:
            if rank([[walsh(x,a) for a in A] for x in outside])<s:
                answer=weight; patterns.add(U); pair_count += 1
                if n%s==0:
                    D={a^b for a in A for b in A}
                    H=D; K=[x for x in G if all(walsh(x,h)==1 for h in H)]
                    rigid &= len(H)==s and is_subgroup(H) and tuple(sorted(U[0]^x for x in K))==U
                    # In the equality case nullity is one and hence the
                    # unique minimizing line is the modulated indicator.
                    rigid &= rank([[walsh(x,a) for a in A] for x in outside])==s-1
    assert answer is not None
    if n%s==0:
        cosets=subgroup_cosets(n,s)
        pred=min(sum(weights[x] for x in U) for U in cosets)
        assert answer==pred and rigid
        assert patterns=={U for U in cosets if sum(weights[x] for x in U)==pred}
    return {'s':s,'minimum_weight':answer,'minimum_fraction':str(F(answer,sum(weights))),
            'minimizing_support_patterns':len(patterns),'minimizing_A_U_pairs':pair_count,
            'rigidity_checked':n%s==0}


def prime(n):
    return n>=2 and all(n%d for d in range(2,isqrt(n)+1))


def balanced_prime_example():
    """Three distinct actual primes in each quadratic sign pattern mod 105."""
    qs=(3,5,7); buckets=[[] for _ in range(8)]
    p=2
    while min(map(len,buckets))<3:
        if prime(p) and gcd(p,105)==1:
            x=sum((pow(p%q,(q-1)//2,q)!=1)<<i for i,q in enumerate(qs))
            if len(buckets[x])<3: buckets[x].append(p)
        p+=1
    for i,ps in enumerate(buckets):
        for p in ps:
            assert prime(p) and gcd(p,105)==1
            assert all(walsh(i,1<<j)==(1 if pow(p%q,(q-1)//2,q)==1 else -1)
                       for j,q in enumerate(qs))
    flat=[p for ps in buckets for p in ps]
    assert len(set(flat))==24
    biases=[sum(len(ps)*walsh(x,a) for x,ps in enumerate(buckets)) for a in range(1,8)]
    assert biases==[0]*7
    return {'modulus':105,'quadratic_basis_moduli':qs,'primes_by_negative_sign_bitmask':buckets,
            'sample_size':len(flat),'nonprincipal_numerators':biases}


def main():
    checks=check_constants()
    # Exact Haar sample and a nonuniform distribution with tiny nonzero bias.
    # With weights 10^6 at each point except one extra count, each nontrivial
    # mean has absolute value 1/(8*10^6+1), below eta even for s=8.
    n=8; w=[10**6]*n; w[3]+=1
    assert F(1,sum(w)) <= F(1,1000*8**3)
    out={'constant_checks_for_integer_s':checks,
         'walsh_group_order':n,
         'uniform_distances':[exact_minimum([1]*n,s) for s in range(2,n+1)],
         'tiny_bias_weights':w,
         'tiny_bias_distances':[exact_minimum(w,s) for s in range(2,n+1)],
         'actual_prime_example':balanced_prime_example(),
         'status':'All exact checks passed. Illustration only; not a verification of the analytic theorem.'}
    print(json.dumps(out,indent=2))

if __name__=='__main__': main()
