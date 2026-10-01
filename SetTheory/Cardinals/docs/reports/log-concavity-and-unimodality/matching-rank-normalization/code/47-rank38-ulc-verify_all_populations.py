"""Exact all-population Hall-gap certificate; standard library only.

The calculation is a coefficient verification, not a parameter sample.
Finite differences in n-b and the binomial basis in m cover both unbounded
integer exterior populations. Run with --max-rank 38 for the stated range.
"""
from argparse import ArgumentParser
from collections import defaultdict
from hashlib import sha256
from math import comb
from pathlib import Path
import json
import time
from population_coeff import population_coefficient, T
from difference_coeff import finite_differences

def verify_rank(r):
    start=time.monotonic()
    records=[]
    for a in range(3,r-2):
        b=r-a
        for k in range(2,r-1):
            digest=sha256()
            stats=defaultdict(int, positive=0, zero=0)
            min_positive=None
            for s in range(max(0,2*k-2*a),min(2*b,2*k)+1):
                L=2*k-s
                for p in range(L//2+1):
                    vals=[population_coefficient(a,b,b+i,k,s,p) for i in range(s+1)]
                    cs=finite_differences(vals)
                    stats['polynomials']+=1
                    for d,c in enumerate(cs):
                        if c<0:
                            raise AssertionError(('negative coefficient',a,b,k,s,p,d,c))
                        stats['coefficients']+=1
                        stats['positive' if c else 'zero']+=1
                        stats['max_bits']=max(stats['max_bits'],c.bit_length())
                        if c and (min_positive is None or c<min_positive):
                            min_positive=c
                        digest.update(f'{s},{p},{d}:{c}\n'.encode('ascii'))
            records.append({'a':a,'b':b,'k':k,**dict(stats),
                            'smallest_positive':min_positive,
                            'coefficient_sha256':digest.hexdigest()})
        # No subsequent core pair needs these polynomial values.
        T.cache_clear()
    return {'rank':r,'core_pairs':r-5,'gaps':len(records),
            'polynomials':sum(x['polynomials'] for x in records),
            'coefficients':sum(x['coefficients'] for x in records),
            'positive':sum(x['positive'] for x in records),
            'zero':sum(x['zero'] for x in records),
            'elapsed_seconds':round(time.monotonic()-start,3),'records':records}

if __name__=='__main__':
    parser=ArgumentParser()
    parser.add_argument('--min-rank',type=int,default=6)
    parser.add_argument('--max-rank',type=int,default=38)
    parser.add_argument('--output-dir',type=Path,default=Path(__file__).parent/'certificate')
    args=parser.parse_args()
    args.output_dir.mkdir(exist_ok=True)
    for r in range(args.min_rank,args.max_rank+1):
        result=verify_rank(r)
        (args.output_dir/f'rank_{r:02d}.json').write_text(json.dumps(result,indent=2)+'\n')
        print({k:v for k,v in result.items() if k!='records'},flush=True)
