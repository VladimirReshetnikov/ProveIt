#!/usr/bin/env python3
"""Evaluate an explicitly supplied tuple; this program does not search for zeros."""
from pathlib import Path
import argparse
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT/'code'))
from arithmetic import evaluate

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('tuple', help='JSON array file, or - for stdin')
    p.add_argument('--domain', choices=['positive','natural','integer'],default='positive')
    p.add_argument('--value', action='store_true', help='Also print the entire integer in decimal')
    args = p.parse_args()
    names = dict(positive='carrier65',natural='natural14',integer='integer42')
    graph = json.loads((ROOT/'equation'/(names[args.domain]+'.json')).read_text())
    data = json.loads(sys.stdin.read() if args.tuple=='-' else Path(args.tuple).read_text())
    if not isinstance(data,list) or len(data)!=len(graph['witnesses']):
        raise ValueError('Expected exactly '+str(len(graph['witnesses']))+' coordinates')
    if any(type(x) is not int for x in data):
        raise ValueError('All coordinates must be integers; booleans are not allowed')
    if args.domain=='positive' and any(x<=0 for x in data):
        raise ValueError('Positive-domain coordinates must all be greater than zero')
    if args.domain=='natural' and any(x<0 for x in data):
        raise ValueError('Natural-domain coordinates must all be nonnegative')
    env = dict(zip(graph['witnesses'],data))
    for port,file in graph['coefficient_binding']['ports'].items():
        env[port]=int.from_bytes((ROOT/'equation/coefficients'/file).read_bytes(),'big')
    value=evaluate(graph,env)[graph['output']]
    magnitude=abs(value).to_bytes(max(1,(abs(value).bit_length()+7)//8),'big')
    result={'domain':graph['witness_domain'],'coordinates':len(data),
            'zero':value==0,'sign':(value>0)-(value<0),
            'absolute_bit_length':abs(value).bit_length(),
            'absolute_big_endian_sha256':hashlib.sha256(magnitude).hexdigest()}
    if args.value:
        if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
        result['value']=str(value)
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__':
    main()
