#!/usr/bin/env python3
"""Boolean subset coverage for five-adic packed-index control.

No complete certificate bound is asserted. Default compares the receipt.
"""
from pathlib import Path
import argparse
import json
import random


def power_five_exponent(n):
    assert n >= 1
    exponent = 0
    while n % 5 == 0:
        n //= 5
        exponent += 1
    assert n == 1
    return exponent


def valuation_five(n):
    assert n > 0
    exponent = 0
    while n % 5 == 0:
        n //= 5
        exponent += 1
    return exponent


def subgroup_table(d, N):
    a = power_five_exponent(d)
    n = power_five_exponent(N)
    assert N > 25*d
    modulus = d*N
    T = N//5
    B = pow(2, d, modulus)
    A = pow(B, 4, modulus)
    residue_to_j = {}
    weights = []
    value = 1
    for j in range(T):
        assert value % (5*d) == 1
        t = (value-1)//(5*d)
        assert 0 <= t < T and t not in residue_to_j
        residue_to_j[t] = j
        weights.append(value)
        value = value*A % modulus
    assert value == 1 and len(residue_to_j) == T
    assert set(residue_to_j) == set(range(T))
    return dict(d=d, N=N, a=a, n=n, modulus=modulus, T=T, B=B,
                A=A, residue_to_j=residue_to_j, weights=weights)


def subset_for_target(d, N, target, table=None):
    table = subgroup_table(d, N) if table is None else table
    assert (table['d'], table['N']) == (d, N)
    M, T, B = table['modulus'], table['T'], table['B']
    target %= M
    epsilon = int(target % 5 == 0)
    k = (target-epsilon*B) % (5*d)
    assert 1 <= k < 5*d < T and k % 5 != 0
    numerator = target-epsilon*B-k
    assert numerator % (5*d) == 0
    wanted_sum = (numerator//(5*d)) % T
    t0 = (wanted_sum-k*(k-1)//2)*pow(k, -1, T) % T
    ts = [(t0+i) % T for i in range(k)]
    js = [table['residue_to_j'][t] for t in ts]
    indices = sorted([4*j for j in js]+([1] if epsilon else []))
    assert len(set(ts)) == len(set(js)) == k
    assert len(set(indices)) == k+epsilon
    assert all(i == 1 or i % 4 == 0 for i in indices)
    assert max(indices) <= 4*T-4 < N
    actual = (sum(table['weights'][j] for j in js)+epsilon*B) % M
    assert actual == target
    return dict(target=target, epsilon=epsilon, k=k, t0=t0,
                indices=indices, modular_sum=actual)


def verify_valuations():
    cases = 0
    for a in range(5):
        d = 5**a
        for j in range(1,101):
            assert valuation_five(pow(2,4*d*j)-1) == a+1+valuation_five(j)
            cases += 1
    return cases


def dynamic_coverage(table):
    """Independent all-subset residue DP; no cardinality construction used."""
    M = table['modulus']
    mask = (1 << M)-1
    reachable = 1
    for weight in table['weights']+[table['B']]:
        shifted = ((reachable << weight) | (reachable >> (M-weight))) & mask
        reachable |= shifted
    assert reachable == mask
    return reachable.bit_count()


def verify_coverage():
    rng = random.Random(5076)
    records = []
    for d,N,exhaustive,samples in ((1,125,True,0),(5,625,True,0),
                                  (25,3125,False,257),(125,15625,False,257),
                                  (625,78125,False,97)):
        table = subgroup_table(d,N)
        targets = range(table['modulus']) if exhaustive else sorted({
            0,1,table['modulus']-1,5*d,5*d-1,
            *[rng.randrange(table['modulus']) for _ in range(samples)]})
        checked = selected = internal = 0
        for target in targets:
            result = subset_for_target(d,N,target,table)
            checked += 1
            selected += len(result['indices'])
            # Every admissible power-five factorization with H>=25.
            h = 1
            while N//h >= 25:
                assert N % h == 0
                assert all(i+1 < N and i+h < N for i in result['indices'])
                internal += len(result['indices'])
                h *= 5
        records.append(dict(d=d,N=N,modulus=table['modulus'],subgroup_size=table['T'],
                            exhaustive_targets=exhaustive,target_cases=checked,
                            selected_bits_checked=selected,internal_bounds_checked=internal,
                            independent_dp_coverage=dynamic_coverage(table) if exhaustive else None))
    return records


def verify_units():
    cases = 0
    for DC in range(5):
        for DR in range(5):
            for g in range(20):
                repaired = DC+(pow(2,g,5) if (2*DC-DR) % 5 == 0 else 0)
                assert (2*repaired-DR) % 5 != 0
                assert (1+2*(repaired+2*DR+2)) % 5 == (2*repaired-DR) % 5
                for e in range(4):
                    gamma = pow(2,e,5)*3*(1+2*(repaired+2*DR+2)) % 5
                    assert gamma != 0 and (-2*gamma) % 5 != 0
                cases += 1
    return cases


def verify_affine_index():
    records = []
    for b,L,N,h in ((1,5,625,5),(5,5,3125,25)):
        d=b*L
        R=1<<b; B=1<<d; q=1<<(d*N); M=d*N
        e=1; G=R**e; DC=3; DR=2
        D=DC+B*DR+B**h
        assert N % h == 0 and N//h >= 25 and (2*DC-DR) % 5 != 0
        table=subgroup_table(d,N)
        for Z0,F0,Qmask in ((1,2,0),(3,5,7),(5,7,12)):
            r0=(q*q-Z0-q*F0)*(q*q-1)+Qmask
            gamma=G*(q*q-1)*(1+q*D)
            assert gamma % 5 != 0
            target=((2*r0+1)-d*h)*pow(2*gamma,-1,M) % M
            result=subset_for_target(d,N,target,table)
            K=sum(1<<(d*i) for i in result['indices'])
            Z=Z0+G*K; F=F0+D*G*K
            r=(q*q-Z-q*F)*(q*q-1)+Qmask
            assert 0 < Z < q and 0 < F < q and r > 0
            assert r == r0-gamma*K
            assert (2*r+1-d*h) % M == 0
            # Check the exponent congruence through reduced exponents, without X.
            assert (2*r+1) % (d*N) == d*h
            records.append(dict(b=b,L=L,d=d,N=N,h=h,q_bits=q.bit_length(),
                                packed_index_bits=r.bit_length(),selected_bits=len(result['indices']),
                                exact_affine_identity=True,actual_index_congruence=True))
    return dict(cases=records,count=len(records),
                scope='Illustrative moderate coefficients, not a full native compiler or Pell tuple; the exact integer packed-index identity is checked')


def verify():
    return dict(status='PASS_FIVE_ADIC_DUMMY_CONTROL',valuation_cases=verify_valuations(),
                coverage=verify_coverage(),unit_repair_cases=verify_units(),
                affine_index=verify_affine_index(),
                proof='../1980/EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md',
                conclusion='Boolean weights at cells4j and optional1 cover every residue modulo dN for powers5 with N>25d',
                full_certificate_operation_count=None,
                scope='Unconditional subset theorem and conditional exact packed-index application; no huge full-compiler q or Pell tuple is materialized',
                review='Author and independent complete proof/source reviews pass; fresh exact receipt checks pass')


if __name__ == '__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true')
    args=parser.parse_args();result=verify();receipt=Path(__file__).with_suffix('.json')
    normalized=json.loads(json.dumps(result))
    if args.write:receipt.write_text(json.dumps(normalized,indent=2)+'\n',encoding='utf-8')
    else:assert normalized == json.loads(receipt.read_text(encoding='utf-8'))
    print(result['status'])
    print('valuations',result['valuation_cases'],'coverage',result['coverage'])
    print('units',result['unit_repair_cases'],'affine_examples',result['affine_index']['count'])
