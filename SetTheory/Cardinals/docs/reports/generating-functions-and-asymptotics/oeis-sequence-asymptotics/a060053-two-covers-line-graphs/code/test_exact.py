#!/usr/bin/env python3
"""Non-asserting regression tests, equally active under python -O."""
import argparse
from fractions import Fraction
from hashlib import sha256
import json
from math import comb
from pathlib import Path
from exact_counts import MAX_INDEX, bounded_index, counts, first_threshold, decimal, parse_threshold
from endpoint_check import check as endpoint_check
ROOT=Path(__file__).resolve().parents[1]

def equal(a,b,label):
    if a != b:
        raise ArithmeticError('test failure: '+label)

def require_error(fn,label):
    try: fn()
    except ValueError: return
    raise ArithmeticError('missing input rejection: '+label)

def run(cap,endpoint=5):
    if not 80 <= cap <= MAX_INDEX:
        raise ValueError('test cap must be between 80 and 640')
    seq=counts(cap)
    frozen=json.loads((ROOT/'data/exact80.json').read_text())
    for name,values in frozen.items():
        equal([decimal(v) for v in seq[name][:81]],values,'independent exact80 '+name)
    files={'V':'A060053_bfile.txt','U':'A014500_bfile.txt','legacy':'A132219_bfile.txt'}
    ranges={}
    for name,file in files.items():
        seen=[]
        for line in (ROOT/'sources'/file).read_text().splitlines():
            if not line.strip() or line.startswith('#'): continue
            n,value=map(int,line.split()[:2])
            if n <= cap:
                equal(seq[name][n],value,f'{name} source n={n}')
                seen.append(n)
        ranges[name]=[min(seen),max(seen),len(seen)]
    # An independent exact identity, across the entire requested range.
    for n in range(cap+1):
        equal(seq['U'][n],sum(comb(n,k)*seq['V'][k] for k in range(n+1)),f'binomial transform n={n}')
    rows=endpoint_check(endpoint)
    frozen_rows=json.loads((ROOT/'data/endpoints6.json').read_text())
    equal(rows,frozen_rows[:endpoint+1],'endpoint fixture')
    equal(first_threshold([3,1,4],2)['index'],0,'nonmonotone finite scan')
    equal(first_threshold([0,1,2],3),None,'bounded scan not found')
    equal(first_threshold(seq['V'],2)['index'],3,'V threshold plateau')
    equal(parse_threshold('1'+'0'*3000),10**3000,'long threshold parser')
    equal(decimal(10**3000),'1'+'0'*3000,'long integer rendering')
    for bad in ('','-1','0','1'*4001,'12x'):
        require_error(lambda:parse_threshold(bad),'threshold text')
    for bad in (-1,MAX_INDEX+1,True,1.5):
        require_error(lambda:bounded_index(bad),'index')
    for bad in (0,-1,True,1.5):
        require_error(lambda:first_threshold([1,2],bad),'threshold')
    encoded=json.dumps({k:[decimal(v) for v in values] for k,values in seq.items()},sort_keys=True,separators=(',',':')).encode()
    return {'cap':cap,'endpoint_cap':endpoint,'source_checks':ranges,'count_data_sha256':sha256(encoded).hexdigest(),
            'last_digits':{k:len(decimal(v[-1]).split('/')[0]) for k,v in seq.items()},'status':'passed'}

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--cap',type=int,default=100)
    ap.add_argument('--endpoint-cap',type=int,choices=range(7),default=5)
    args=ap.parse_args()
    print(json.dumps(run(args.cap,args.endpoint_cap),indent=2,sort_keys=True))
