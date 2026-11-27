#!/usr/bin/env python3
"""Exact finite tests for paper.tex; no third-party packages.

Every asserted combinatorial equality is tested with integer arithmetic or Fraction.
The optional prime counts are empirical examples, not certificates of GRH.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product
from math import comb, gcd, isqrt
from pathlib import Path
import json
import random


def vectors(p, r):
    return list(product(range(p), repeat=r))


def directions(p, r):
    """Represent lines by the vector whose first nonzero coordinate is 1."""
    return [v for v in vectors(p, r) if next((a for a in v if a), 0) == 1]


def dot(x, v, p):
    return sum(a*b for a, b in zip(x, v)) % p


def local_counts(c, v, p):
    n = [0]*p
    for x, w in c.items():
        n[dot(x, v, p)] += w
    return n


def signed(a, c):
    d = Counter(a)
    d.subtract(c)
    return {x: m for x, m in d.items() if m}


def density(c, p, r):
    ds = directions(p, r)
    bad = sum(any(local_counts(c, v, p)) for v in ds)
    return Fraction((p-1)*bad, p**r)


def digits(p, k):
    a, power = 0, 1
    while power*p <= k:
        power *= p
        a += 1
    return a, k//power


def lower(p, r, k):
    if k >= p**(r-1):
        return Fraction(p-1, p**r)
    a, b = digits(p, k)
    return Fraction((p-1)*(p+1-b), p**(a+2))


def valid_digit(p, b):
    return (p-1) % b == 0 or (p+1) % b == 0


def primitive_root(p):
    for g in range(1, p):
        if len({pow(g, i, p) for i in range(p-1)}) == p-1:
            return g
    raise AssertionError('no generator')


def split(p, b):
    g = primitive_root(p)
    B = [pow(g, i*(p-1)//b, p) for i in range(b)]
    return [(a, 0) for a in B], [(0, a) for a in B]


def nonsplit(p, b):
    """Identify z=(a,b) with a+b*sqrt(d); trace pairing is (2a,2db)."""
    d = next(i for i in range(1, p) if pow(i, (p-1)//2, p) == p-1)
    def mul(z, w):
        a, b = z
        c, e = w
        return ((a*c+d*b*e) % p, (a*e+b*c) % p)
    G = [(a, b) for a, b in vectors(p, 2) if (a*a-d*b*b) % p == 1]
    assert len(G) == p+1
    for g in G:
        powers = [(1, 0)]
        for _ in range(p):
            powers.append(mul(powers[-1], g))
        if len(set(powers)) == p+1:
            break
    else:
        raise AssertionError('norm-one generator not found')
    B = powers[::(p+1)//b]
    assert len(B) == b and len(set(B)) == b
    beta = g
    assert beta not in B
    pair = lambda z: ((2*z[0]) % p, (2*d*z[1]) % p)
    return [pair(z) for z in B], [pair(mul(beta,z)) for z in B]


def lift(p, r, a, A, C):
    assert r >= a+2
    def one(S):
        return [u+x+(0,)*(r-a-2) for u in vectors(p,a) for x in S]
    return one(A), one(C)


def saturated(p, r):
    U = vectors(p,r-1)
    return [u+(0,) for u in U], [u+(1,) for u in U]


def verify_constructions():
    results = []
    for p in (3,5,7,11,13,17,19):
        for b in range(1,p):
            for case, fn, modulus in [('split',split,p-1),('nonsplit',nonsplit,p+1)]:
                if modulus % b:
                    continue
                A,C = fn(p,b)
                assert len(A)==len(C)==b and len(set(A))==len(set(C))==b
                assert set(A).isdisjoint(C)
                # Cover planar constructions and higher-rank lifts without huge tests.
                for r,a in [(2,0),(3,0),(3,1)]:
                    if p**r>7000:
                        continue
                    AA,CC=lift(p,r,a,A,C)
                    h=b*p**a
                    actual=density(signed(AA,CC),p,r)
                    expected=lower(p,r,h)
                    assert actual==expected, (p,r,b,a,case,actual,expected)
                    results.append(dict(p=p,r=r,a=a,b=b,construction=case,h=h,delta=str(actual)))
        for r in (1,2,3):
            if p**r>7000:
                continue
            A,C=saturated(p,r)
            actual=density(signed(A,C),p,r)
            assert actual==Fraction(p-1,p**r)
            results.append(dict(p=p,r=r,construction='saturation',h=len(A),delta=str(actual)))
    return results


def exhaustive_planar(p, k, max_agree):
    """All multisets, no quotienting or assumptions about support.

    A collision in signatures on a set of m projective directions is equivalent
    to an agreeing pair on all m. Test every set of max_agree+1 directions,
    and exhibit a collision on max_agree directions. This is much faster than
    enumerating all pairs. A signature encodes the entire projected histogram.
    """
    xs=vectors(p,2)
    ds=directions(p,2)
    dots=[[dot(x,v,p) for x in xs] for v in ds]
    # Encode a histogram in base k+1 by summing one digit for each packet entry.
    weights=[[(k+1)**j for j in row] for row in dots]
    signatures=[]
    for inds in combinations_with_replacement(range(len(xs)),k):
        signatures.append(tuple(sum(row[i] for i in inds) for row in weights))
    assert len(signatures)==comb(p*p+k-1,k)
    assert len(set(signatures))==len(signatures)
    tested=0
    for sub in combinations(range(p+1),max_agree+1):
        seen=set()
        for s in signatures:
            key=tuple(s[j] for j in sub)
            assert key not in seen,(p,k,sub,'unexpected agreement')
            seen.add(key)
        tested+=1
    witness=None
    for sub in combinations(range(p+1),max_agree):
        seen={}
        for i,s in enumerate(signatures):
            key=tuple(s[j] for j in sub)
            if key in seen:
                witness=(seen[key],i,sub)
                break
            seen[key]=i
        if witness is not None:
            break
    assert witness is not None
    i,j,sub=witness
    actual_agree=sum(a==b for a,b in zip(signatures[i],signatures[j]))
    assert actual_agree==max_agree
    return dict(p=p,r=2,k=k,packets=len(signatures),forbidden_direction_subsets=tested,
                maximum_matching_directions=max_agree,delta=str(Fraction((p-1)*(p+1-max_agree),p*p)),
                collision_indices=[i,j],matching_direction_indices=list(sub))


def exhaustive_small_rank3(p,k):
    xs=vectors(p,3)
    ds=directions(p,3)
    weights=[[(k+1)**dot(x,v,p) for x in xs] for v in ds]
    signatures=[tuple(sum(row[i] for i in inds) for row in weights)
                for inds in combinations_with_replacement(range(len(xs)),k)]
    m=max(sum(x==y for x,y in zip(a,b)) for a,b in combinations(signatures,2))
    delta=Fraction((p-1)*(len(ds)-m),p**3)
    assert delta==lower(p,3,k)
    return dict(p=p,r=3,k=k,packets=len(signatures),pairs=comb(len(signatures),2),delta=str(delta))


def cyclo_coeff(n):
    # reduce sum n_j z^j using z^(p-1)=-1-z-...-z^(p-2)
    return [x-n[-1] for x in n[:-1]]


def divide_pi(g,p):
    """Exact quotient in Z[z]/Phi_p by 1-z, or None if not divisible."""
    total=sum(g)
    if total%p:
        return None
    last=total//p
    out=[]
    prefix=0
    for i,a in enumerate(g):
        prefix+=a
        out.append(prefix-(i+1)*last)
    assert out[-1]==last
    # independently multiply back by (1-z) modulo Phi_p
    back=[out[0]+out[-1]]+[out[i]-out[i-1]+out[-1] for i in range(1,p-1)]
    assert back==g
    return out


def valuation(g,p):
    if not any(g):
        return None
    t=0
    while True:
        q=divide_pi(g,p)
        if q is None:
            return t
        g=q
        t+=1


def leading(g,p,t):
    for _ in range(t):
        g=divide_pi(g,p)
        assert g is not None
    return sum(g)%p


def verify_valuation():
    rng=random.Random(20261127)
    checked=0
    by_prime=Counter()
    max_t=Counter()
    for p in (3,5,7):
        for r in (2,3):
            vs=vectors(p,r)
            for _ in range(30):
                k=rng.randint(1,min(3*p,35))
                c=signed(rng.choices(vs,k=k),rng.choices(vs,k=k))
                if not c:
                    continue
                h=sum(x for x in c.values() if x>0)
                a,b=digits(p,h)
                gs={v:cyclo_coeff(local_counts(c,v,p)) for v in vs}
                vals=[valuation(g,p) for g in gs.values() if any(g)]
                assert vals and max(vals)<=a*(p-1)+b
                t=min(vals)
                f={v:leading(g,p,t) for v,g in gs.items()}
                assert any(f.values()) and f[(0,)*r]==0
                for v in vs:
                    for lam in range(1,p):
                        assert f[tuple(lam*x%p for x in v)]==pow(lam,t,p)*f[v]%p
                # Check multivariate Newton coefficients of degree > t vanish.
                for alpha in vs:
                    if sum(alpha)<=t:
                        continue
                    value=0
                    for j in product(*(range(x+1) for x in alpha)):
                        coeff=1
                        for u,v in zip(alpha,j):
                            coeff*=comb(u,v)*(-1)**(u-v)
                        value+=coeff*f[j]
                    assert value%p==0
                actual=density(c,p,r)
                assert actual>=lower(p,r,h)
                checked+=1
                by_prime[p]+=1
                max_t[p]=max(max_t[p],t)
    return dict(seed=20261127,cases=checked,by_prime=dict(by_prime),largest_minimum_valuation=dict(max_t))


def obstruction_7_5():
    """Independent check of the nonattainment at (p,r,k)=(7,2,5).

    If two disjoint size-five packets agree in five directions, the
    point-through-directions counting argument forces them to be sets.
    A projective linear change maps the complementary three directions
    to infinity, slope 0 and slope 1. Translate one positive point to 0.
    The negative set has one nonzero point on each of slopes 2,...,6.
    Exhaust all 6^5 possibilities, checking the other positive candidates.
    This does not use the classification of 3-nets.
    """
    p=7
    allowed=set(range(2,7))
    xs=vectors(p,2)
    sl={v:(v[1]*pow(v[0],-1,p)%p if v[0] else -1)
        for v in xs if v!=(0,0)}
    # For each possible negative point, record all eligible positive points
    # and the cross direction. The origin is among them by construction.
    rows=[[(t,m*t%p) for t in range(1,p)] for m in sorted(allowed)]
    table={z:{a:sl[((a[0]-z[0])%p,(a[1]-z[1])%p)] for a in xs
              if a!=z and sl[((a[0]-z[0])%p,(a[1]-z[1])%p)] in allowed}
           for row in rows for z in row}
    most=0
    count=0
    for C in product(*rows):
        possible=set(table[C[0]])
        for z in C[1:]:
            possible.intersection_update(table[z])
        eligible=[a for a in possible if len({table[z][a] for z in C})==5]
        assert (0,0) in eligible
        most=max(most,len(eligible))
        assert len(eligible)<5, (C,eligible)
        count+=1
    assert count==6**5
    return dict(p=p,r=2,k=5,negative_sets_checked=count,
                maximum_eligible_positive_points=most,nonattainment=True)


def sieve(n):
    a=bytearray(b'\x01')*(n+1)
    a[:2]=b'\x00\x00'
    for p in range(2,isqrt(n)+1):
        if a[p]:
            a[p*p:n+1:p]=b'\x00'*((n-p*p)//p+1)
    return [i for i in range(n+1) if a[i]]


def arithmetic_examples():
    primes=sieve(200000)
    results=[]
    for p,mods,b,construction,pad in [(3,(7,13),2,'split',0),
                                    (5,(11,31),3,'nonsplit',0),
                                    (7,(29,43),4,'nonsplit',1)]:
        Q=mods[0]*mods[1]
        logs=[]
        for q in mods:
            assert (q-1)%p==0
            g=primitive_root(q)
            logs.append({pow(g,i,q):i%p for i in range(q-1)})
        fn=split if construction=='split' else nonsplit
        A,C=fn(p,b)
        # The last example is a size-5 pair by common padding of size one.
        A=A+[(0,0)]*pad
        C=C+[(0,0)]*pad
        c=signed(A,C)
        bad={v for v in vectors(p,2) if any(local_counts(c,v,p))}
        quot=lambda n:tuple(logs[i][n%q] for i,q in enumerate(mods))
        classes=[n for n in range(1,Q) if gcd(n,Q)==1]
        quotient_counts=Counter(quot(n) for n in classes)
        assert len(quotient_counts)==p*p and len(set(quotient_counts.values()))==1
        class_bad=sum(quot(n) in bad for n in classes)
        exact=Fraction(class_bad,len(classes))
        assert exact==density(c,p,2)
        ps=[n for n in primes if gcd(n,Q)==1]
        npbad=sum(quot(n) in bad for n in ps)
        results.append(dict(p=p,Q=Q,k=len(A),h=b,construction=construction,
                            positive_packet=A,negative_packet=C,
                            reduced_residue_classes=len(classes),disagreeing_classes=class_bad,
                            exact_density=str(exact),prime_cutoff=200000,
                            unramified_primes=len(ps),disagreeing_primes=npbad,
                            empirical_fraction=str(Fraction(npbad,len(ps)))))
    return results


def main():
    data={}
    data['constructions']=verify_constructions()
    data['exhaustive_planar']=[exhaustive_planar(p,k,min(k,p))
                              for p in (3,5) for k in range(1,p+1)]
    data['exhaustive_rank3']=[exhaustive_small_rank3(3,k) for k in (1,2)]
    data['valuation_tests']=verify_valuation()
    data['obstruction_7_5']=obstruction_7_5()
    data['arithmetic_examples']=arithmetic_examples()
    data['note']='Exact finite assertions passed; prime frequencies are illustrative, not used in proofs.'
    out=Path(__file__).with_name('verification.json')
    out.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
    print('Construction cases:',len(data['constructions']))
    print('Exhaustive planar cases:',len(data['exhaustive_planar']))
    print('Planar packet enumerations:',sum(x['packets'] for x in data['exhaustive_planar']))
    print('Exhaustive rank-3 pairs:',sum(x['pairs'] for x in data['exhaustive_rank3']))
    print('Valuation cases:',data['valuation_tests']['cases'])
    print('Exponent-seven obstruction:',data['obstruction_7_5'])
    for x in data['arithmetic_examples']:
        print('Q=%d, p=%d, k=%d: exact=%s, observed=%s' %(x['Q'],x['p'],x['k'],x['exact_density'],x['empirical_fraction']))
    print('All checks passed.')

if __name__=='__main__':
    main()
