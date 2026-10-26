#!/usr/bin/env python3
"""Exactly evaluate one delivered polynomial at a supplied positive tuple.

Print only sign, zero status and bit length, since the value can be huge.
This is an evaluator, not a search for a zero or a consistency decision.
"""
from pathlib import Path
import argparse
import gzip
import json

ROOT=Path(__file__).resolve().parent


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('point',type=Path,help='JSON array of ten positive integers')
    ap.add_argument('--equation',default='centered_transport88',
                    choices=['trace_inverse85','square_transport85','lower_center87',
                             'centered_transport88','quotient_center96'])
    args=ap.parse_args()
    values=json.loads(args.point.read_text())
    if not isinstance(values,list) or len(values)!=10 or any(type(x) is not int or x<=0 for x in values):
        raise ValueError('point must be ten strictly positive integers')
    g=json.loads((ROOT/'equations'/(args.equation+'.json')).read_text())
    env=dict(zip(g['witnesses'],values))
    for name,item in g['coefficient_binding']['ports'].items():
        env[name]=int.from_bytes(gzip.decompress((ROOT/g['coefficient_binding']['path']/item['file']).read_bytes()),'little')
    def arg(x):return x if type(x) is int else env[x]
    for name,op,x,y in g['source']:
        a,b=arg(x),arg(y)
        env[name]=a+b if op=='+' else a-b if op=='-' else a*b
    p=env[g['output']]
    print(json.dumps({'equation':args.equation,'zero':p==0,
                     'sign':0 if p==0 else 1 if p>0 else -1,
                     'absolute_bit_length':abs(p).bit_length()},indent=2))


if __name__=='__main__':main()
