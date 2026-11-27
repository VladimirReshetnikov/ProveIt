#!/usr/bin/env python3
"""Exact finite checks for prime-labelled binary codes (standard library only).

The examples are illustrations, not a test of the asymptotic GRH estimate.
Sampling uses the polynomial window in the paper, with integer weights.
All subsequent Legendre symbols, ranks and weight enumerators are exact.
"""
from __future__ import annotations
import argparse, csv, json, math, random
from pathlib import Path


def primes_to(n):
    sieve = bytearray(b'\x01') * (n + 1)
    sieve[:2] = b'\x00\x00'
    for p in range(2, math.isqrt(n) + 1):
        if sieve[p]:
            sieve[p*p:n+1:p] = b'\x00' * ((n-p*p)//p+1)
    return [i for i in range(2, n+1) if sieve[i]]


def is_prime(p):
    return p >= 2 and all(p % d for d in range(2, math.isqrt(p)+1))


def window_sample(pool, x, count, rng):
    # w(p/x)=(p-x)^4(2*x-p)^4/x^8.  Common denominator cancels.
    vals = [p for p in pool if x < p < 2*x]
    weights = [(p-x)**4*(2*x-p)**4 for p in vals]
    # The proof samples i.i.d. and rejects whole lists with duplicates.
    cumul = []
    total = 0
    for w in weights:
        total += w
        cumul.append(total)
    from bisect import bisect_right
    while True:
        out = [vals[bisect_right(cumul, rng.randrange(total))] for _ in range(count)]
        if len(set(out)) == count:
            return out


def legendre_bit(p, q):
    t = pow(p % q, (q-1)//2, q)
    assert t in (1, q-1), (p,q,t)
    return int(t != 1)


def row_masks(qs, ps):
    return [sum(legendre_bit(p,q) << j for j,p in enumerate(ps)) for q in qs]


def rref(rows, n):
    a = list(rows); piv = []; rank = 0
    for j in range(n):
        pivot = next((i for i in range(rank,len(a)) if (a[i] >> j) & 1), None)
        if pivot is None: continue
        a[rank],a[pivot] = a[pivot],a[rank]
        for i in range(len(a)):
            if i != rank and (a[i] >> j) & 1: a[i] ^= a[rank]
        piv.append(j); rank += 1
    return a[:rank], piv


def kernel_basis(rows, n):
    a,piv = rref(rows,n)
    basis=[]
    for j in range(n):
        if j in piv: continue
        v=1<<j
        for row,k in zip(a,piv):
            if (row>>j)&1: v |= 1<<k
        basis.append(v)
    return basis


def weight_enum(basis,n):
    out=[0]*(n+1); v=0; out[0]=1
    for k in range(1,1<<len(basis)):
        v ^= basis[(k & -k).bit_length()-1]
        out[v.bit_count()] += 1
    return out


def distance(enum):
    return next((i for i in range(1,len(enum)) if enum[i]), None)


def macwilliams(a,k,n):
    # B_j=2^-k sum_i A_i K_j(i).
    def comb(N,K): return math.comb(N,K) if 0<=K<=N else 0
    out=[]
    for j in range(n+1):
        num=sum(a[i]*sum((-1)**l*comb(i,l)*comb(n-i,j-l) for l in range(j+1)) for i in range(n+1))
        assert num%(1<<k)==0
        out.append(num//(1<<k))
    return out


def rank_defect_all(rows,n):
    # Exact enumeration of every rectangle, for n <= 12 in shipped checks.
    r=len(rows); best=-1; arg=None; examined=0
    for I in range(1<<r):
        rr=[rows[i] for i in range(r) if (I>>i)&1]; a=len(rr)
        for J in range(1<<n):
            b=J.bit_count(); rank=len(rref([row&J for row in rr],n)[1])
            d=min(a,b)-rank; examined+=1
            if d>best: best=d; arg=(I,J,rank)
    I,J,rank=arg
    return {'rectangles_examined':examined,'maximum_defect':best,
            'witness_rows_0based':[i for i in range(r) if I>>i&1],
            'witness_columns_0based':[j for j in range(n) if J>>j&1], 'witness_rank':rank}


def certify(qs,ps,all_rectangles=False):
    assert len(set(qs+ps)) == len(qs)+len(ps)
    assert all(p>2 and is_prime(p) for p in qs+ps)
    n=len(ps); rows=row_masks(qs,ps); rr,piv=rref(rows,n)
    assert len(rr)==len(qs), 'rank-deficient matrix'
    ker=kernel_basis(rows,n)
    assert len(ker)==n-len(qs)
    assert all((v&u).bit_count()%2==0 for v in ker for u in rows)
    assert len(rref(ker,n)[1])==len(ker)
    # Independent Legendre-symbol check by explicit quadratic residue sets.
    for q,row in zip(qs,rows):
        sq={k*k%q for k in range(1,q)}
        assert all(((row>>j)&1)==int(p%q not in sq) for j,p in enumerate(ps))
    a=weight_enum(rr,n); b=weight_enum(ker,n)
    assert sum(a)==1<<len(qs) and sum(b)==1<<len(ker)
    assert macwilliams(a,len(qs),n)==b
    result={'r':len(qs),'n':n,'q_primes':qs,'p_primes':ps,
            'matrix_rows':[''.join(str((row>>j)&1) for j in range(n)) for row in rows],
            'rank':len(rr),'distance':distance(a),'dual_distance':distance(b),
            'weight_enumerator':a,'dual_weight_enumerator':b,'macwilliams_verified':True}
    if all_rectangles: result['rectangles']=rank_defect_all(rows,n)
    return result


def generate():
    rng=random.Random(20261127)
    result=[]
    for n,r,x,attempts,fixed in [(12,6,300,60,False),(24,12,1500,80,False),
                                 (32,16,3000,20,False),(24,12,2500,80,True)]:
        pool=primes_to(6*x); best=None; score=(-1,-1)
        for _ in range(attempts):
            qs=pool[1:r+1] if fixed else window_sample(pool,x,r,rng)
            ps=window_sample(pool,3*x,n,rng)
            rows=row_masks(qs,ps); rr,piv=rref(rows,n)
            if len(rr)!=r: continue
            d=distance(weight_enum(rr,n)); e=distance(weight_enum(kernel_basis(rows,n),n))
            cand=(min(d,e),d+e)
            if cand>score: best=(qs,ps); score=cand
        assert best
        item=certify(*best,all_rectangles=(n<=12)); item.update({'X':x,'fixed_prefix':fixed,'trials':attempts})
        result.append(item)
    return {'seed':20261127,'examples':result}


def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--regenerate',action='store_true'); args=parser.parse_args()
    root=Path(__file__).resolve().parent; path=root/'examples.json'
    if args.regenerate:
        data=generate(); path.write_text(json.dumps(data,indent=2)+'\n')
    data=json.loads(path.read_text())
    for e in data['examples']:
        got=certify(e['q_primes'],e['p_primes'],'rectangles' in e)
        assert all(e[k]==v for k,v in got.items())
        assert all(3*e['X']<p<6*e['X'] for p in e['p_primes'])
        if e['fixed_prefix']:
            assert e['q_primes']==primes_to(max(e['q_primes']))[1:]
        else:
            assert all(e['X']<q<2*e['X'] for q in e['q_primes'])
        print(f"[n={e['n']}, k={e['r']}, d={e['distance']}, d_dual={e['dual_distance']}] prefix={e['fixed_prefix']} exact checks PASS")
        if 'rectangles' in e: print('  '+str(e['rectangles']))
    print('All certificates checked, including exact MacWilliams identities.')
    if args.regenerate:
        with (root/'examples_summary.csv').open('w',newline='') as f:
            fields=['n','r','distance','dual_distance','rank','X','fixed_prefix','trials']
            wr=csv.DictWriter(f,fields); wr.writeheader(); wr.writerows({k:e[k] for k in fields} for e in data['examples'])

if __name__=='__main__': main()
