#!/usr/bin/env python3
"""Small exact checks for analytic.tex, not proofs of universal statements.

Prime-reciprocal construction checks keep its enormous bound symbolically
as the exponent of 2; they do not enumerate primes up to that bound.
"""
from fractions import Fraction
from itertools import product
from math import gcd, isqrt, prod
from pathlib import Path
import json


def primes_up_to(n):
    flags = [True] * (n+1)
    if n >= 0:
        flags[0] = False
    if n >= 1:
        flags[1] = False
    for p in range(2, isqrt(n)+1):
        if flags[p]:
            for m in range(p*p, n+1, p):
                flags[m] = False
    return [p for p in range(2, n+1) if flags[p]]


def power_two(e):
    return Fraction(2**e, 1) if e >= 0 else Fraction(1, 2**(-e))


def mobius(n):
    if n == 1:
        return 1
    mu = 1
    for p in primes_up_to(n):
        if n % p == 0:
            if n % (p*p) == 0:
                return 0
            mu = -mu
    return mu


def zeta_partial(s, n):
    return sum((Fraction(1, j**s) for j in range(1, n+1)), Fraction(0))


def euler_partial(s, n):
    return prod((Fraction(p**s, p**s-1) for p in primes_up_to(n)), start=Fraction(1))


def partition_blocks(xs):
    blocks = []
    for x in xs:
        if not blocks or sum(blocks[-1], Fraction(0)) + x > Fraction(3, 4):
            blocks.append([x])
        else:
            blocks[-1].append(x)
    return blocks


def check():
    counts = {}
    cheb_cases = 0
    for k in range(3, 15):
        n = 2**k
        ps = primes_up_to(n)
        assert 2**(k-1) <= k*len(ps) <= 6*2**k
        ell = (k+1)//2
        assert ell*2**ell <= 2**k
        assert prod(ps) <= 2**(2**(k+1)-2)
        cheb_cases += 1
    counts['dyadic_chebyshev_K_3_through_14'] = cheb_cases

    block_cases = 0
    vals = [Fraction(j, 8) for j in range(5)]
    for length in range(5):
        for xs in product(vals, repeat=length):
            blocks = partition_blocks(xs)
            total = sum(xs, Fraction(0))
            k = (total.numerator+total.denominator-1)//total.denominator
            assert len(blocks) <= 4*k+1
            assert all(sum(b, Fraction(0)) <= Fraction(3,4) for b in blocks)
            assert all(sum(b, Fraction(0)) > Fraction(1,4) for b in blocks[:-1])
            value = prod((1/(1-x) for x in xs), start=Fraction(1))
            assert value <= 4**len(blocks) <= 4**(4*k+1)
            block_cases += 1
    counts['greedy_block_product_exact_rational_lists'] = block_cases

    # Formal arithmetic of B(k)=2^(2*C), C=4^(4*k+1), with B kept symbolic.
    for k in range(31):
        c = 4**(4*k+1)
        exponent_of_b = 2*c
        harmonic_lower_bound = 1 + Fraction(exponent_of_b, 2)
        assert harmonic_lower_bound == 1+c and harmonic_lower_bound > c
    counts['prime_reciprocal_bound_symbolic_exponent_checks_k_0_through_30'] = 31

    euler_cases = 0
    tail_cases = 0
    truncation_cases = 0
    for s in range(2, 7):
        for n in range(1, 31):
            z = zeta_partial(s, n)
            e = euler_partial(s, n)
            error = Fraction(1, n**(s-1))
            assert 0 <= e-z <= error
            euler_cases += 1
            for m in (n, n+1, n+5):
                zm = zeta_partial(s, m)
                assert 0 <= zm-z <= error-Fraction(1,m**(s-1)) <= error
                tail_cases += 1
            ps = primes_up_to(n)
            for j in range(5):
                t = prod((sum((Fraction(1,p**(s*h)) for h in range(j+1)),Fraction(0))
                          for p in ps), start=Fraction(1))
                assert t <= z+error
                assert 0 <= e-t <= n*power_two(n-j)
                truncation_cases += 1
    counts['finite_euler_product_error_exact_rational_cases'] = euler_cases
    counts['zeta_tail_exact_rational_cases'] = tail_cases
    counts['finite_euler_truncation_cases'] = truncation_cases
    for n in range(1, 31):
        for d in range(1, 51):
            j = 2*n+d+2
            assert n*power_two(n-j) < Fraction(1,d)
    counts['denominator_based_error_removal_pairs_N_D'] = 1500

    sieve_cases = 0
    for z in range(14):
        ps = primes_up_to(z)
        modulus = prod(ps)
        subset_terms = [(prod(p for p, included in zip(ps,bits) if included), (-1)**sum(bits))
                        for bits in product((0,1), repeat=len(ps))]
        density = prod((1-Fraction(1,p) for p in ps), start=Fraction(1))
        for x in range(65):
            actual = sum(gcd(n, modulus) == 1 for n in range(1,x+1))
            exact = sum(sign*(x//d) for d,sign in subset_terms)
            assert actual == exact
            assert abs(actual-x*density) <= 2**len(ps)
            sieve_cases += 1
    counts['finite_sieve_X_0_through_64_z_0_through_13'] = sieve_cases
    for x in range(2, 201):
        z = isqrt(x)
        ps = primes_up_to(z)
        modulus = prod(ps)
        survivors = sum(gcd(n,modulus) == 1 for n in range(1,x+1))
        assert len(primes_up_to(x)) == survivors+len(ps)-1
    counts['prime_counting_sieve_X_2_through_200'] = 199

    independence_cases = 0
    for r in range(5):
        ps = [2,3,5,7][:r]
        modulus = prod(ps)
        for statuses in product((0,1,2), repeat=r):
            count = sum(all(st == 0 or (st == 1 and n%p == 0) or (st == 2 and n%p != 0)
                            for p,st in zip(ps,statuses)) for n in range(modulus))
            probability = prod((Fraction(1,p) if st == 1 else Fraction(p-1,p) if st == 2
                                else Fraction(1) for p,st in zip(ps,statuses)), start=Fraction(1))
            assert Fraction(count,modulus) == probability
            independence_cases += 1
    counts['CRT_independence_zero_nonzero_unrestricted_patterns'] = independence_cases

    for x in range(1, 61):
        actual = sum(gcd(a,b) == 1 for a in range(1,x+1) for b in range(1,x+1))
        formula = sum(mobius(d)*(x//d)**2 for d in range(1,x+1))
        assert actual == formula
    counts['coprime_pair_Mobius_counts_X_1_through_60'] = 60
    return {'status':'PASS', 'meaning':'Finite implementation checks; not a formal iPRA proof.',
            'huge_bound_policy':'The prime reciprocal upper endpoint B(k) was kept symbolically as a power of two; its prime sum was not evaluated.',
            'counts':counts}


if __name__ == '__main__':
    result = check()
    print(json.dumps(result,indent=2))
    (Path(__file__).resolve().parent/'validation_analytic.json').write_text(json.dumps(result,indent=2)+'\n')
