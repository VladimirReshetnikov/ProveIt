#!/usr/bin/env python3
"""Independently replay expression DAGs and prove their values pairwise distinct.
Only Python's standard library and exact integer/rational arithmetic are used.
No equality between overlapping numerical intervals is ever assumed.
"""
from __future__ import annotations
import argparse, json, math, struct, time
from fractions import Fraction
from pathlib import Path
ROOT = 0xffffffff
RECORD = struct.Struct('<BII')

def verify(path: Path) -> dict:
    raw = path.read_bytes()
    if raw[:8] != b'A158415D' or len(raw) < 25 or (len(raw)-16)%9:
        raise ValueError('Invalid certificate framing.')
    precision, max_n = struct.unpack_from('<II', raw, 8)
    if not 32 <= precision <= 4096 or not 1 <= max_n <= 254:
        raise ValueError('Certificate parameters outside safety limits.')
    Q=1 << precision
    low=[]; high=[]; costs=[]; births=[0]*(max_n+1)
    for index, (cost,a,b) in enumerate(RECORD.iter_unpack(raw[16:])):
        if not 1 <= cost <= max_n:
            raise ValueError(f'Invalid cost at record {index}.')
        if index==0:
            if (cost,a,b)!=(1,ROOT,ROOT):
                raise ValueError('The first record must be the leaf 1.')
            l=u=Q
        elif b==ROOT:
            if not a < index or cost != costs[a]+1:
                raise ValueError(f'Invalid radical at record {index}.')
            l=math.isqrt(low[a] << precision)
            v=high[a] << precision
            u=math.isqrt(v); u += u*u < v
        else:
            if not a < index or not b < index or cost != costs[a]+costs[b]+1:
                raise ValueError(f'Invalid addition at record {index}.')
            l=low[a]+low[b]; u=high[a]+high[b]
        if not Q <= l <= u:
            raise ValueError(f'Invalid enclosure at record {index}.')
        low.append(l); high.append(u); costs.append(cost); births[cost]+=1
    order=sorted(range(len(low)), key=low.__getitem__)
    min_gap=None
    for a,b in zip(order,order[1:]):
        gap=low[b]-high[a]
        if gap<=0:
            raise ValueError(f'Intervals {a} and {b} are not disjoint.')
        if min_gap is None or gap < min_gap: min_gap=gap
    total=0; counts=[]
    for n in range(1,max_n+1):
        total+=births[n]; counts.append(total)
    lower=Fraction(46551,25000)  # exactly 1.86204
    z=1/lower
    margin=z*(1+sum(Fraction(births[n])*z**(n+1)
                    for n in range(1,max_n+1)))-1
    result={
        'verified_records':len(low), 'precision_bits':precision,
        'sample_counts_at_most_n':counts,
        'birth_counts_by_assigned_cost':births[1:],
        'pairwise_disjoint_intervals':True,
        'min_gap_numerator':str(min_gap), 'gap_denominator_power_of_two':precision,
        'min_gap_display':float(Fraction(min_gap,Q)) if min_gap is not None else None,
        'claimed_lower_constant':'1.86204',
        'lower_inequality_verified':margin>0,
        'lower_polynomial_margin_display':float(margin),
        'proves_completeness':False,
    }
    if max_n==28 and margin<=0:
        raise ValueError('The advertised lower-bound inequality did not verify.')
    return result

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate',nargs='?',type=Path,
                        default=Path(__file__).parent/'data'/'digit_sample.bin')
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    start=time.monotonic(); result=verify(args.certificate)
    result['runtime_seconds_in_this_run']=round(time.monotonic()-start,3)
    text=json.dumps(result,indent=2)+'\n'
    print(text,end='')
    if args.output:args.output.write_text(text)
