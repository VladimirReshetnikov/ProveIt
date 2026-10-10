#!/usr/bin/env python3
"""Recompute every exact residual enclosure and compare rational endpoints.

Unlike a hash-only receipt check, this reruns the rational mathematics.
Elapsed times and display-only decimal strings are not used as evidence.
"""
from fractions import Fraction as Q
from pathlib import Path
import json
from certified_euler import evaluate
from verify_s4 import verify as verify_primary
from verify_s4_independent import verify as verify_independent

ROOT=Path(__file__).resolve().parents[1]

def main():
    cert=ROOT/'data/S4_certificate.json'
    checks=[verify_primary(cert),verify_independent(cert)]
    for p,filename in [(4,'S4_interval_N1000.json'),(6,'S6_interval_N1000.json'),
                       (8,'S8_exclusion_N1000.json')]:
        saved=json.loads((ROOT/'data'/filename).read_text())
        fresh=evaluate(saved['N'],p)
        for field in ['N','p','schema','identity','contains_zero']:
            if saved[field]!=fresh[field]:raise AssertionError(f'{filename}: {field}')
        for side in ['lower','upper']:
            if Q(saved['residual'][side])!=Q(fresh['residual'][side]):
                raise ArithmeticError(f'{filename}: residual {side}')
        if saved['values'].keys()!=fresh['values'].keys():raise AssertionError('Value set')
        for name in saved['values']:
            for side in ['lower','upper']:
                if Q(saved['values'][name][side])!=Q(fresh['values'][name][side]):
                    raise ArithmeticError(f'{filename}: {name} {side}')
        lo,hi=(Q(saved['residual'][side]) for side in ['lower','upper'])
        if p==4:
            assert lo<=0<=hi and hi-lo<Q('7.109e-299')
        elif p==6:
            assert Q('-1.357e-299')<lo<=0<=hi<Q('1.515e-299')
            assert hi-lo<Q('2.871e-299')
        else:
            assert Q('-1.3274179020580459e-86')<lo<=hi<Q('-1.3274179020580457e-86')
            assert hi-lo<Q('2.080e-290')
        checks.append({'file':filename,'result':'PASS','rational_endpoints':'exact match'})
    result={'result':'PASS','checks':checks,
            'note':'Enclosures containing zero do not prove an identity.'}
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
