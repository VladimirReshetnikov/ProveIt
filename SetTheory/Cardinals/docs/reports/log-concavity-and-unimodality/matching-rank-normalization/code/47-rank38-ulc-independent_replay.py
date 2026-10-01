"""Independent exact replay of the Hall all-population certificate.

No imports from the certificate generator.  Support counts are propagated by
adding exterior vertices, T(j,q;n+1)=T(j,q;n)+T(j-1,q;n), rather than recomputed
from its defining binomial sum.  Newton coordinates use the explicit inverse
Pascal matrix, rather than repeated subtraction.  Every per-gap field and
SHA-256 digest is compared with the original manifest.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import time

# All indices in this certificate are at most 114.
C = [[math.comb(n,k) for k in range(n+1)] for n in range(160)]
def choose(n,k):
    return C[n][k] if n >= 0 and 0 <= k <= n else 0


def support_table(a,b):
    # Indexed by (q,j), with each value listing the support counts at n=b+i.
    # Initial condition counts disjoint selected A and L sets directly.
    current = [[sum(choose(a,q+x)*choose(b,j-x)
                    for x in range(j+1)) for j in range(b+1)]
               for q in range(a+1)]
    table = {(q,j):[current[q][j]] for q in range(a+1) for j in range(b+1)}
    for n in range(b,3*b):
        nxt = [[current[q][j]+(current[q][j-1] if j else 0)
                for j in range(b+1)] for q in range(a+1)]
        for q in range(a+1):
            for j in range(b+1):
                table[q,j].append(nxt[q][j])
        current=nxt
    zero=[0]*(2*b+1)
    def get(order,j):
        return table.get((order-j,j),zero)
    return get


def replay_pair(a,b,expected):
    r=a+b
    T=support_table(a,b)
    records=[]
    for k in range(2,r-1):
        digest=hashlib.sha256()
        polynomials=coefficients=positive=zeros=max_bits=0
        minimum=None
        lo=max(0,2*(k-a)); hi=min(2*b,2*k)
        for s in range(lo,hi+1):
            total_degree=2*k-s
            # Build the two product polynomials by exterior population value.
            # This changes the loop order and never calls the old G evaluator.
            terms=[]
            for j in range(max(0,s-b),min(b,s)+1):
                j2=s-j
                mass=choose(b,j)*choose(b,j2)
                left,right=T(k,j),T(k,j2)
                below,above=T(k-1,j),T(k+1,j2)
                square=[k*(r-k)*mass*left[i]*right[i] for i in range(s+1)]
                adjacent=[(k+1)*(r-k+1)*mass*below[i]*above[i] for i in range(s+1)]
                terms.append((j,square,adjacent))
            for overlap in range(total_degree//2+1):
                union=total_degree-overlap
                free=total_degree-2*overlap
                values=[0]*(s+1)
                for j,square,adjacent in terms:
                    aa=choose(free,k-j-overlap)
                    bb=choose(free,k-1-j-overlap)
                    if aa or bb:
                        for i in range(s+1):
                            values[i]+=aa*square[i]-bb*adjacent[i]
                factor=choose(union,overlap)
                # Explicit inverse Pascal transform, independently of the
                # original finite-difference subtraction implementation.
                newton=[factor*sum((-1 if (d-i)&1 else 1)*C[d][i]*values[i]
                                   for i in range(d+1)) for d in range(s+1)]
                polynomials+=1
                for d,value in enumerate(newton):
                    if value<0:
                        raise RuntimeError(('NEGATIVE',a,b,k,s,overlap,d,value))
                    coefficients+=1
                    positive+=bool(value)
                    zeros+=not value
                    max_bits=max(max_bits,value.bit_length())
                    if value and (minimum is None or value<minimum): minimum=value
                    digest.update(f'{s},{overlap},{d}:{value}\n'.encode('ascii'))
        actual=dict(a=a,b=b,k=k,positive=positive,zero=zeros,
                    polynomials=polynomials,coefficients=coefficients,
                    max_bits=max_bits,smallest_positive=minimum,
                    coefficient_sha256=digest.hexdigest())
        target=expected.get((a,b,k))
        if target is None:
            raise RuntimeError(('MISSING GAP IN MANIFEST',a,b,k))
        if actual!=target:
            raise RuntimeError(('MANIFEST MISMATCH',actual,target))
        records.append(actual)
    return records


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--min-rank',type=int,default=6)
    parser.add_argument('--max-rank',type=int,default=38)
    parser.add_argument('--original',type=Path,default=Path(__file__).resolve().parent.parent/'data'/'certificate')
    parser.add_argument('--output',type=Path,default=Path(__file__).parent/'replay')
    args=parser.parse_args(); args.output.mkdir(exist_ok=True)
    for r in range(args.min_rank,args.max_rank+1):
        start=time.monotonic()
        source=args.original/f'rank_{r:02d}.json'
        if not source.exists(): raise RuntimeError(('missing original manifest',source))
        old=json.loads(source.read_text())
        expected={(x['a'],x['b'],x['k']):x for x in old['records']}
        records=[]
        for a in range(3,r-2): records.extend(replay_pair(a,r-a,expected))
        if len(records)!=len(expected): raise RuntimeError('gap-count mismatch')
        result=dict(rank=r,core_pairs=r-5,gaps=len(records),
                    **{field:sum(x[field] for x in records) for field in
                       ('polynomials','coefficients','positive','zero')},
                    elapsed_seconds=round(time.monotonic()-start,3),
                    all_gap_hashes_match=True,records=records)
        for field in ('core_pairs','gaps','polynomials','coefficients','positive','zero'):
            if result[field]!=old[field]: raise RuntimeError(('rank-count mismatch',r,field))
        (args.output/f'rank_{r:02d}.json').write_text(json.dumps(result,indent=2)+'\n')
        print({key:value for key,value in result.items() if key!='records'},flush=True)

if __name__=='__main__': main()
