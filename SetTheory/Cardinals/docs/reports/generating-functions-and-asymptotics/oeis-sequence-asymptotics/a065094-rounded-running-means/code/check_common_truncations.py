#!/usr/bin/env python3
"""Prove common truncations from exact rational intervals, not printed endpoints."""
from fractions import Fraction as F
from pathlib import Path
import json
import sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).absolute().parent.parent
sys.path.insert(0,str(ROOT))
from verify_manifest import load_json,read_regular
from certify_amplitudes import compute,check,fixed_decimal


def common_truncation(lower,upper,digits):
    check(type(digits) is int and digits>=0 and 0<=lower<=upper,'invalid truncation inputs')
    scale=10**digits
    l=lower.numerator*scale//lower.denominator
    u=upper.numerator*scale//upper.denominator
    check(l==u,'interval crosses requested truncation boundary')
    return fixed_decimal(F(l,scale),digits)


def generate(reference=None):
    intervals={}
    cert=compute(intervals=intervals)
    if reference is None:reference=load_json(read_regular(ROOT/'certificates/amplitude_certificate.json'))
    check(cert==reference,'published certificate differs')
    result={}
    for mode in ('floor','ceiling'):
        result[mode]={}
        for key,(lower,upper) in intervals[mode].items():
            printed=cert['sequences'][mode][key]
            fractional=[s.split('.')[1] for s in printed]
            common=0
            for x,y in zip(*fractional):
                if x!=y:break
                common+=1
            result[mode][key]={'rational_interval_common_truncated_places':69,
                               'common_truncation_69':common_truncation(lower,upper,69),
                               'displayed_70_place_endpoint_common_prefix_places':common}
    check(result['ceiling']['A']['displayed_70_place_endpoint_common_prefix_places']==68,'unexpected printed A+ endpoint prefix')
    return {'status':'PASS','N':10000,'arithmetic':'integer and Fraction only',
            'method':'floor(10^69 lower)==floor(10^69 upper) on exact rational intervals',
            'sequences':result}


if __name__=='__main__':print(json.dumps(generate(),indent=2,sort_keys=True))
