#!/usr/bin/env python3
"""Exact-arithmetic tests for signed binomial coefficient supercongruences.

Python 3.9+; standard library only. Run from any directory:
    python code/verify.py --output results

The tests are finite checks, NOT a formal proof. The accompanying paper gives
an all-parameter proof using the classical Jacobsthal binomial congruence.
"""
from __future__ import annotations

import argparse
import csv
import json
import platform
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import comb
from pathlib import Path
from random import Random
from time import perf_counter
from typing import Optional


def require(condition: bool, message: str) -> None:
    """Assertions that remain enabled when Python is run with -O."""
    if not condition:
        raise AssertionError(message)


def binomial(top: int, bottom: int) -> int:
    """Generalized integer binomial, with the ordinary formal-series convention."""
    if bottom < 0:
        return 0
    if top >= 0:
        return comb(top, bottom) if bottom <= top else 0
    return (-1 if bottom % 2 else 1) * comb(bottom - top - 1, bottom)


def exact_div(numerator: int, denominator: int) -> int:
    quotient, remainder = divmod(numerator, denominator)
    require(remainder == 0, f"Nonexact division: denominator={denominator}")
    return quotient


def binomial_row(top: int, length: int) -> list[int]:
    result = [1]
    for k in range(1, length + 1):
        result.append(exact_div(result[-1] * (top - k + 1), k))
    return result


def coefficient_convolution(plus: int, minus: int, degree: int) -> int:
    """[x^degree](1+x)^plus(1-x)^minus, by binomial convolution."""
    if degree < 0:
        raise ValueError("degree must be nonnegative")
    left = binomial_row(plus, degree)
    right = binomial_row(minus, degree)
    return sum((-1 if j % 2 else 1) * right[j] * left[degree-j]
               for j in range(degree + 1))


def coefficient_recurrence(plus: int, minus: int, degree: int) -> int:
    """Independent evaluator from (1-x^2)F'=((plus-minus)-(plus+minus)x)F.

    This performs exact integer divisions, never modular divisions by k.
    """
    if degree < 0:
        raise ValueError("degree must be nonnegative")
    previous, current = 0, 1  # coefficients of degrees -1 and 0
    for k in range(1, degree + 1):
        following = exact_div((plus-minus)*current + (k-2-plus-minus)*previous, k)
        previous, current = current, following
    return current


@lru_cache(maxsize=8192)
def sequence(r: int, s: int, t: int, n: int) -> int:
    if n < 0 or t < 0:
        raise ValueError("n and t must be nonnegative")
    a = coefficient_convolution(r*n, s*n, t*n)
    b = coefficient_recurrence(r*n, s*n, t*n)
    require(a == b, f"Evaluator disagreement at {(r,s,t,n)}")
    return a


def valuation(value: int, p: int) -> Optional[int]:
    """None represents v_p(0)=infinity."""
    if value == 0:
        return None
    exponent = 0
    while value % p == 0:
        value //= p
        exponent += 1
    return exponent


def mobius(n: int) -> int:
    if n < 1:
        raise ValueError("n must be positive")
    sign, divisor = 1, 2
    while divisor * divisor <= n:
        if n % divisor == 0:
            n //= divisor
            sign = -sign
            if n % divisor == 0:
                return 0
            while n % divisor == 0:
                n //= divisor
        divisor += 1
    return -sign if n > 1 else sign


def run_family_tests() -> tuple[list[dict], dict]:
    rows: list[dict] = []
    grid_cases = [(5,1,1),(5,1,2),(5,1,5),(7,1,1),(11,1,3),
                  (13,1,1),(5,2,1),(5,2,2),(7,2,1),(5,3,1),(7,3,1)]
    three_cases = [(3,1,1),(3,1,2),(3,2,1),(3,3,1),(3,4,1)]

    def check(r: int, s: int, t: int, p: int, h: int, m: int, suite: str) -> None:
        high, low = m*p**h, m*p**(h-1)
        delta = sequence(r,s,t,high) - sequence(r,s,t,low)
        exponent = 3*h - (1 if p == 3 else 0)
        modulus = p**exponent
        require(delta % modulus == 0,
                f"Counterexample: {(r,s,t,p,h,m)} residue {delta % modulus}")
        rows.append(dict(suite=suite,r=r,s=s,t=t,p=p,h=h,m=m,
                         high_index=high,low_index=low,required_exponent=exponent,
                         actual_valuation=valuation(delta,p),zero_difference=(delta==0),
                         passed=True))

    for r,s,t in product(range(-6,7),range(-6,7),range(5)):
        for p,h,m in grid_cases:
            check(r,s,t,p,h,m,"grid_p_ge_5")
        for p,h,m in three_cases:
            check(r,s,t,p,h,m,"grid_p_3")
    rng = Random(352373)
    random_cases = [(p,h,m) for p in (3,5,7,11,13) for h in (1,2,3)
                    for m in (1,2,3) if m*p**h <= 400]
    for _ in range(150):
        p,h,m = rng.choice(random_cases)
        check(rng.randint(-15,15),rng.randint(-15,15),rng.randint(1,5),
              p,h,m,"seeded_random")
    for r,s,t in [(-1,-3,1),(-1,-2,1),(-1,-2,2),(-2,-4,1),(1,2,1)]:
        for p,h,m in [(5,4,1),(3,5,1),(7,3,2),(11,3,1)]:
            check(r,s,t,p,h,m,"focused_deep")
    stats = dict(total=len(rows), by_suite=dict(Counter(row['suite'] for row in rows)),
                 nonzero_differences=sum(not row['zero_difference'] for row in rows),
                 zero_differences=sum(row['zero_difference'] for row in rows),
                 all_passed=True, random_seed=352373,
                 grid_parameters={"r":[-6,6],"s":[-6,6],"t":[0,4]},
                 grid_prime_cases=grid_cases,grid_three_cases=three_cases,
                 max_high_index=max(row['high_index'] for row in rows))
    return rows, stats


def run_lemma_tests() -> dict:
    counts: Counter = Counter()
    rng = Random(352373)
    for p in (3,5,7,11):
        for h in (1,2,3):
            if p**h > 350:
                continue
            modulus = p**h
            for a in (-3,-1,0,1,3):
                for k in range(3*modulus+1):
                    lhs = binomial(a*modulus-1,k)
                    rhs = (-1)**(k-k//p)*binomial(a*modulus//p-1,k//p)
                    require((lhs-rhs)%modulus == 0,"Binomial descent failure")
                    counts['binomial_descent'] += 1
            for level in range(1,h+1):
                P = p**level
                for q in range(5):
                    H = sum((-1)**j*pow(j*j,-1,P)
                            for j in range(q*P,(q+1)*P) if j%p)
                    require(H%P == 0,"Alternating harmonic block failure")
                    counts['harmonic_blocks'] += 1
            for _ in range(15):
                a,b,c = rng.randrange(-4,5),rng.randrange(-4,5),rng.randrange(1,4)
                A,B,K = a*modulus,b*modulus,c*modulus
                target = p**(3*h-(1 if p==3 else 0))
                fine = [(-1)**j*binomial(B,j)*binomial(A,K-j) for j in range(K+1)]
                for j in range(0,K+1,p):
                    coarse = (-1)**(j//p)*binomial(B//p,j//p)*binomial(A//p,(K-j)//p)
                    require((fine[j]-coarse)%target==0,"Multiple-index term failure")
                    counts['multiple_index_terms'] += 1
                offsum = sum(fine[j] for j in range(1,K) if j%p)
                require(offsum%p**(3*h)==0,"Off-multiple cancellation failure")
                counts['off_multiple_sums'] += 1
                W = sum((-1)**j*pow(j*j,-1,modulus)*binomial(B-1,j-1)
                        *binomial(A-1,K-j-1) for j in range(1,K) if j%p)%modulus
                require(W==0,"Weighted cancellation failure")
                counts['weighted_sums'] += 1
                Ts = []
                for level in range(1,h+1):
                    P = p**level
                    weight = [binomial(B//P-1,q)*binomial(A//P-1,K//P-1-q)
                              for q in range(K//P)]
                    T = sum((-1)**j*pow(j*j,-1,modulus)*weight[j//P]
                            for j in range(1,K) if j%p)%modulus
                    Ts.append(T)
                require((W+Ts[0])%modulus==0,"Initial negative sign failure")
                counts['initial_weight_sign'] += 1
                for index in range(len(Ts)-1):
                    require((Ts[index]-Ts[index+1])%modulus==0,
                            "Multiscale weighted descent failure")
                    counts['multiscale_transitions'] += 1
                require(Ts[-1]==0,"Terminal block failure")
                counts['terminal_blocks'] += 1
    return dict(counts=counts,total=sum(counts.values()),all_passed=True,
                random_seed=352373)


def run_mobius_tests() -> dict:
    examples=[]
    checks=0
    for r,s,t in [(-1,-3,1),(-1,-2,1),(-1,-2,2),(-2,-4,1),(1,2,1)]:
        for n in range(1,101):
            numerator=sum(mobius(d)*sequence(r,s,t,n//d) for d in range(1,n+1) if n%d==0)
            b=Fraction(numerator,n**3)
            denominator=(3*b).denominator
            require(denominator & (denominator-1) == 0,
                    f"3*b_n denominator is not a power of 2: {(r,s,t,n,b)}")
            if (r,s,t)==(-1,-3,1) and n<=12:
                examples.append(dict(n=n,b=str(b)))
            checks+=1
    return dict(total=checks,all_passed=True,A352373_examples=examples)


def examples_and_boundaries() -> dict:
    samples=[]
    for p,h in [(5,1),(5,2),(5,3),(7,1),(3,1),(3,2),(2,1)]:
        delta=sequence(-1,-3,1,p**h)-sequence(-1,-3,1,p**(h-1))
        samples.append(dict(p=p,h=h,difference=str(delta),valuation=valuation(delta,p)))
    require(sequence(-1,-3,1,5)-sequence(-1,-3,1,1)==3250,"Sharpness example")
    require(sequence(-1,-3,1,3)-sequence(-1,-3,1,1)==72,"p=3 boundary")
    require(sequence(-1,-3,1,2)-sequence(-1,-3,1,1)==10,"p=2 boundary")
    trinomial5=sum(comb(5,2*k)*comb(2*k,k) for k in range(3))
    require(trinomial5==51 and (trinomial5-1)%125!=0,"Quadratic boundary")
    return dict(A352373=samples,central_trinomial={"value_at_1":1,"value_at_5":51,
                                               "difference":50,"modulus_failed":125})


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path('results'))
    args=parser.parse_args()
    args.output.mkdir(parents=True,exist_ok=True)
    start=perf_counter()
    rows,family=run_family_tests()
    print(f"Family congruences: {family['total']} passed",flush=True)
    lemmas=run_lemma_tests()
    print(f"Proof-component checks: {lemmas['total']} passed",flush=True)
    transforms=run_mobius_tests()
    examples=examples_and_boundaries()
    result=dict(status='all tests passed',python=platform.python_version(),
                elapsed_seconds=round(perf_counter()-start,3),
                family=family,lemmas=lemmas,mobius_transform=transforms,
                examples=examples,
                caution='Finite exact tests; not a formal verification of the proof.')
    (args.output/'verification.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    with (args.output/'family_cases.csv').open('w',newline='',encoding='utf-8') as handle:
        writer=csv.DictWriter(handle,fieldnames=list(rows[0]))
        writer.writeheader();writer.writerows(rows)
    print(json.dumps({key:result[key] for key in ('status','python','elapsed_seconds')},indent=2))


if __name__=='__main__':
    main()
