#!/usr/bin/env python3
"""Exact finite coefficient checks for the logarithmic spectral bridge.

The endpoint recurrence in model.py is inherited and credited. These are
regression checks, not a proof of the joint asymptotic or its uniform range.
"""
from functools import lru_cache
from hashlib import sha256
from math import comb
from pathlib import Path
import json
from model import EndpointCounter, catalans

MODEL_HASH = 'c693d80529b69762600edc4b4d271155e6aa12c9127bda9a59a839ee143538f7'


@lru_cache(None)
def block_weight(k, d):
    if k == 1:
        return 1
    return sum(j*comb(2*k-j-3,k-2)//(k-1)
               for j in range(1,min(d,k-1)+1))


def renewal(weights, limit):
    values=[1]+[0]*limit
    for n in range(1,limit+1):
        values[n]=sum(weight*values[n-k]
                      for k,weight in enumerate(weights,1) if k<=n)
    return values


def main():
    root=Path(__file__).parent
    assert sha256((root/'model.py').read_bytes()).hexdigest()==MODEL_HASH
    limit=80
    C=catalans(limit)
    rows=[]
    comparisons=tight=lower_comparisons=0
    for m in range(1,21):
        u=renewal(C[:m],limit)
        upper=[1]+[sum(u[j]*u[n-1-j] for j in range(n)) for n in range(1,limit+1)]
        counter=EndpointCounter(limit,m)
        d=(m-1).bit_length()
        lower=renewal([block_weight(k,d) for k in range(1,m-d+1)],limit) if m>=2 else None
        digest=sha256()
        for n in range(1,limit+1):
            actual=counter.T(n,n-1,n-1)
            assert actual<=upper[n],(m,n,actual,upper[n])
            comparisons+=1
            if n<=m+1:
                assert actual==upper[n]==C[n],(m,n)
                tight+=1
            if lower is not None:
                assert lower[n]<=actual,(m,n,lower[n],actual)
                lower_comparisons+=1
            digest.update(f'{n}:{actual}:{upper[n]}:{None if lower is None else lower[n]}\n'.encode())
        rows.append(dict(m=m,d=d,largest_n=limit,count_at_largest_n=str(counter.count()),
                         upper_at_largest_n=str(upper[-1]),
                         lower_at_largest_n=None if lower is None else str(lower[-1]),
                         coefficient_sha256=digest.hexdigest()))
        counter.T.cache_clear();counter.unrestricted.cache_clear()
    tail_checks=0
    for m in range(2,257):
        d=(m-1).bit_length()
        for k in range(1,m+1):
            cat=comb(2*(k-1),k-1)//k
            ck=block_weight(k,d)
            assert 0<=cat-ck
            assert 2**d*(cat-ck)<=(d+2)*cat
            tail_checks+=1
    result=dict(status='passed',arithmetic='exact integers',model_sha256=MODEL_HASH,
                source_commit='7421a4ca60fdf125411edf412f825aac54278b37',
                upper_comparisons=comparisons,lower_comparisons=lower_comparisons,
                catalan_equality_checks=tight,uniform_coefficient_checks=tail_checks,
                rows=rows,scope='Finite regression only; the manuscript proves all-index and asymptotic statements.')
    (root/'envelope_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='rows'},sort_keys=True))


if __name__=='__main__':
    main()
