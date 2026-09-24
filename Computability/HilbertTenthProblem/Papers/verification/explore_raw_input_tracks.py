#!/usr/bin/env python3
"""Raw numeric input tracks and finite checks for loader obstructions."""
from fractions import Fraction
from itertools import product
from math import prod
from pathlib import Path
import json


def packed_word(bits, R):
    return sum(bit*R**j for j,bit in enumerate(bits))


def prime_divisors(n):
    result, p = set(), 2
    while p*p <= n:
        if n%p == 0:
            result.add(p)
            while n%p == 0:
                n//=p
        p+=1
    if n>1:
        result.add(n)
    return result


def valuation(n,p):
    assert n>0
    v=0
    while n%p == 0:
        n//=p
        v+=1
    return v


def step(program,n):
    for i,f in enumerate(program):
        if n%f.denominator == 0:
            return i,n//f.denominator*f.numerator
    return None,n


def verify():
    decompositions = 0
    native_identities = 0
    by_radix = []
    for k,max_m in ((2,3),(3,3),(4,3),(6,2),(7,2)):
        R=1<<k
        cases=0
        for m in range(1,max_m+1):
            q=R**m
            J=(q-1)//(R-1)
            tracks=[packed_word(bits,R) for bits in product(range(2),repeat=m)]
            seen=set()
            for I in product(tracks,repeat=k):
                x=sum((1<<i)*a for i,a in enumerate(I))
                assert x not in seen and 0<=x<q
                seen.add(x)
                for i,a in enumerate(I):
                    expected=sum(((x>>(k*j+i))&1)*R**j for j in range(m))
                    assert a==expected
                native=[J+2*a for a in I]
                assert all(a>0 for a in native)
                assert sum((1<<i)*a for i,a in enumerate(native)) == q-1+2*x
                cases+=1
                native_identities+=1
            assert len(seen)==q
        decompositions+=cases
        by_radix.append({'radix':R,'tracks':k,'complete_cases':cases,
                         'input_link_operations':2*(k-1),
                         'generic_positive_adapter_additions':k,
                         'native_link_if_qminus1_is_available':2*k})
    dilation_checks=0
    for k in range(2,9):
        R=1<<k
        delta=lambda x:sum(((x>>j)&1)*R**j for j in range(x.bit_length()))
        for n in range(20):
            assert delta(1<<n)==(1<<n)**k
            dilation_checks+=1
        assert delta(3)==R+1<3**k
    programs=[
        [Fraction(3,2),Fraction(1,3)],
        [Fraction(5,2),Fraction(7,3),Fraction(1,5),Fraction(1,7)],
        [Fraction(2,3),Fraction(3,2)],
    ]
    cofactor_cases=transitions=0
    polynomial_cases=0
    for program in programs:
        S=set().union(*(prime_divisors(f.numerator)|prime_divisors(f.denominator)
                        for f in program))
        outside=[p for p in (5,7,11,13,17,19) if p not in S]
        for n in range(1,49):
            for u in outside:
                a,b=n,n*u
                for _ in range(100):
                    ia,anext=step(program,a)
                    ib,bnext=step(program,b)
                    assert ia==ib and bnext==u*anext
                    transitions+=1
                    a,b=anext,bnext
                    if ia is None:
                        break
                cofactor_cases+=1
        loaders=[lambda x:x,lambda x:x*x+1,lambda x:3*x+7,
                 lambda x:(x-5)**2+1]
        for F in loaders:
            for x0 in range(1,26):
                initial=F(x0)
                M=prod(p**(valuation(initial,p)+1) for p in S)
                for t in range(1,5):
                    value=F(x0+M*t)
                    assert value>0
                    assert all(valuation(value,p)==valuation(initial,p) for p in S)
                    a,b=initial,value
                    for _ in range(100):
                        ia,anext=step(program,a)
                        ib,bnext=step(program,b)
                        assert ia==ib
                        assert all(valuation(anext,p)==valuation(bnext,p) for p in S)
                        a,b=anext,bnext
                        if ia is None:
                            break
                    polynomial_cases+=1
    return {'status':'PASS','scope':'Input-link identities and finite corroboration of direct-dilation and bare-FRACTRAN polynomial-loader obstructions; no complete universal history verifier.',
            'proof':'../1980/EXPLORATION_RAW_INPUT_TRACKS.md',
            'complete_unique_track_decompositions':decompositions,
            'native_positive_input_identities':native_identities,
            'by_radix':by_radix,'dilation_power_inputs':dilation_checks,
            'FRACTRAN_cofactor_initializations':cofactor_cases,
            'FRACTRAN_paired_transition_checks':transitions,
            'polynomial_loader_progression_pairs':polynomial_cases,
            'finite_trajectory_limit':100,
            'nontermination_claim':'No finite trajectory cutoff is used to classify a run as nonhalting; only synchronized finite prefixes are checked.',
            'primary_sources':['Korec1996 strong universality input definition',
                               'Neary2015 Lemma9/Table2 input-dependent production',
                               'Conway1987 ordered FRACTRAN stopping semantics']}


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'],result['complete_unique_track_decompositions'],
          'unique track decompositions;',result['polynomial_loader_progression_pairs'],
          'polynomial-loader progression pairs',flush=True)
