#!/usr/bin/env python3
"""Exact finite distributions for a nondegenerate half-block of Sp_{2n}(q).

All probability calculations use Python integers and fractions.Fraction.
The argument q may be any prime power: formulas only use its cardinality.
This program implements independent counting identities, not a proof assistant.
"""
from __future__ import annotations

import argparse
import csv
import json
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path


@lru_cache(None)
def gaussian(n: int, d: int, q: int) -> int:
    if d < 0 or d > n:
        return 0
    d = min(d, n - d)
    num = den = 1
    for i in range(d):
        num *= q ** (n - i) - 1
        den *= q ** (d - i) - 1
    assert num % den == 0
    return num // den


@lru_cache(None)
def gl_order(d: int, q: int) -> int:
    result = 1
    for i in range(d):
        result *= q**d - q**i
    return result


@lru_cache(None)
def sp_order(m: int, q: int) -> int:
    result = q ** (m * m)
    for i in range(1, m + 1):
        result *= q ** (2 * i) - 1
    return result


@lru_cache(None)
def iso_frames(m: int, d: int, q: int) -> int:
    if d < 0 or d > m:
        return 0
    result = 1
    for i in range(d):
        result *= q ** (2 * m - i) - q**i
    return result


@lru_cache(None)
def embedding(n: int, d: int, s: int, q: int) -> int:
    """Embeddings of a fixed d-space of alternating rank 2s into Sp_n space."""
    assert n % 2 == 0
    t = d - 2 * s
    if s < 0 or t < 0 or s > n // 2 or t > n // 2 - s:
        return 0
    return (sp_order(n // 2, q) // sp_order(n // 2 - s, q)) * iso_frames(n // 2 - s, t, q)


@lru_cache(None)
def type_count(n: int, d: int, s: int, q: int) -> int:
    t = d - 2 * s
    if t < 0:
        return 0
    emb = embedding(n, d, s, q)
    if not emb:
        return 0
    aut = sp_order(s, q) * gl_order(t, q) * q ** (2 * s * t)
    assert emb % aut == 0
    return emb // aut


@lru_cache(None)
def e_product(m: int, q: int) -> F:
    result = F(1)
    for i in range(1, m + 1):
        result *= 1 - F(1, q ** (2 * i))
    return result


@lru_cache(None)
def fiber_factor(k: int, q: int) -> F:
    return F(sum(gaussian(2*k, d, q) * iso_frames(k, d, q) for d in range(k+1)), sp_order(k, q))


def invert_kernel_moments(moments: list[F], q: int, even_only: bool = False) -> list[F]:
    """Invert E[Gaussian(nullity,d)] using its triangular coefficient matrix."""
    n = len(moments) - 1
    result = [F(0)] * (n + 1)
    indices = range(n if not even_only else n - n % 2, -1, -1 if not even_only else -2)
    for d in indices:
        result[d] = moments[d] - sum(gaussian(k, d, q) * result[k] for k in range(d+1, n+1))
    assert all(x >= 0 for x in result), result
    assert sum(result) == 1, sum(result)
    for d, moment in enumerate(moments):
        assert sum(gaussian(k, d, q)*result[k] for k in range(d, n+1)) == moment
    return result


@lru_cache(None)
def uniform_nullities(n: int, q: int) -> tuple[F, ...]:
    moments = [F(gaussian(n, d, q), q**(n*d)) for d in range(n+1)]
    return tuple(invert_kernel_moments(moments, q))


def alternating_nullities(n: int, q: int) -> list[F]:
    assert n % 2 == 0
    denominator = q ** (n * (n - 1) // 2)
    result = [F(0)] * (n + 1)
    for d in range(0, n+1, 2):
        count = gaussian(n, d, q) * gl_order(n-d, q) // sp_order((n-d)//2, q)
        result[d] = F(count, denominator)
    assert sum(result) == 1
    return result


def distributions(n: int, q: int, joint: bool = False) -> dict:
    assert n >= 2 and n % 2 == 0 and q >= 2
    block_moments, defect_moments = [], []
    joint_moments = []
    for d in range(n+1):
        assert sum(type_count(n, d, s, q) for s in range(d//2+1)) == gaussian(n, d, q)
        bm = dm = F(0)
        jm = [F(0)] * (n+1)
        for s in range(d//2+1):
            count = type_count(n, d, s, q)
            if not count:
                continue
            emb = embedding(n, d, s, q)
            bm += count * F(emb, embedding(2*n, d, s, q))
            term = count * F(emb, q ** (2*n*d-d*d))
            dm += term
            if joint:
                free = n - 2*d + 2*s
                for c, probability in enumerate(uniform_nullities(free, q)):
                    jm[c] += term * probability
        block_moments.append(bm)
        defect_moments.append(dm)
        if joint:
            joint_moments.append(jm)
    block = invert_kernel_moments(block_moments, q)
    defect = invert_kernel_moments(defect_moments, q, even_only=True)
    uniform = list(uniform_nullities(n, q))
    alternating = alternating_nullities(n, q)
    alpha = e_product(n//2, q)**2 / e_product(n, q)
    likelihood = [alpha * fiber_factor(k, q) for k in range(n//2+1)]
    assert likelihood[0] < 1 and all(x > 1 for x in likelihood[1:])
    assert sum(defect[2*k]*likelihood[k] for k in range(n//2+1)) == 1
    full_tv = sum(defect[2*k]*abs(likelihood[k]-1) for k in range(n//2+1))/2
    assert full_tv == (1-alpha)*defect[0]
    assert alpha*defect[0] == block[0]
    rank_tv = sum(abs(x-y) for x,y in zip(block,uniform))/2
    defect_tv = sum(abs(x-y) for x,y in zip(defect,alternating))/2
    result = dict(q=q, n=n, alpha=alpha, likelihood=likelihood,
                  block_nullity=block, uniform_nullity=uniform,
                  iid_defect_nullity=defect, alternating_nullity=alternating,
                  full_tv=full_tv, rank_tv=rank_tv, defect_tv=defect_tv)
    if joint:
        table = [[F(0)]*(n+1) for _ in range(n+1)]
        for c in range(n+1):
            for d in range(n, -1, -2):
                table[c][d] = joint_moments[d][c] - sum(gaussian(k,d,q)*table[c][k] for k in range(d+2,n+1,2))
                assert table[c][d] >= 0
            assert sum(table[c]) == uniform[c]
            assert sum(table[c][2*k]*likelihood[k] for k in range(n//2+1)) == block[c]
        for d in range(0,n+1,2):
            assert sum(table[c][d] for c in range(n+1)) == defect[d]
        result['iid_joint_nullity_defect'] = table
    return result


def serial(value):
    if isinstance(value, F):
        return {'fraction': str(value), 'decimal': float(value)}
    if isinstance(value, list):
        return [serial(x) for x in value]
    if isinstance(value, dict):
        return {key: serial(item) for key,item in value.items()}
    return value


def constants(q: int, terms: int = 100) -> dict:
    import decimal
    with decimal.localcontext() as ctx:
        ctx.prec = 200
        D = decimal.Decimal
        even = odd = D(1)
        for j in range(1,terms+1):
            even *= 1-D(q)**(-2*j)
            odd *= 1-D(q)**(-(2*j-1))
        # Each omitted product differs from 1 by at most its geometric tail.
        even_tail = D(q)**(-2*(terms+1))/(1-D(q)**-2)
        odd_tail = D(q)**(-(2*terms+1))/(1-D(q)**-2)
        delta = odd*(1-even)
        # Fewer than 500 arithmetic operations on values bounded by 2, at
        # 200 decimal digits. The added rounding allowance is conservative.
        rounding_allowance = D('1e-190')
        error = even_tail + odd_tail + rounding_allowance
        return dict(q=q, even_product=str(even), odd_product=str(odd),
                    gl_product=str(even*odd), delta=str(delta),
                    equal_prior_success=str((1+delta)/2),
                    absolute_error_bound=str(error), terms=terms,
                    decimal_precision=ctx.prec,
                    rounding_allowance=str(rounding_allowance))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--max-n', type=int, default=24)
    ap.add_argument('--q', type=int, nargs='+', default=[2,3,4,5])
    ap.add_argument('--out', type=Path, default=Path(__file__).resolve().parents[1]/'results')
    args = ap.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    rows=[]
    detailed=[]
    for q in args.q:
        for n in range(2,args.max_n+1,2):
            result=distributions(n,q,joint=(n<=8))
            rows.append({key:(float(result[key]) if isinstance(result[key],F) else result[key])
                         for key in ['q','n','alpha','full_tv','rank_tv','defect_tv']})
            if n<=8:
                detailed.append(serial(result))
    with (args.out/'exact_distances.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
    (args.out/'exact_small_distributions.json').write_text(json.dumps(detailed,indent=2)+'\n')
    (args.out/'limiting_constants.json').write_text(json.dumps([constants(q) for q in args.q],indent=2)+'\n')
    summary={'status':'passed','parameter_cases':len(rows),'max_n':args.max_n,'q':args.q,
             'arithmetic':'exact rational','joint_distribution_checks':'all even n <= 8',
             'identities':['type-count sum','kernel-moment inversion','nonnegative normalized distributions',
                           'likelihood normalization','likelihood sign classification','two exact TV identities',
                           'independent joint-law reconstruction of block rank']}
    (args.out/'formula_check_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))


if __name__=='__main__':
    main()
