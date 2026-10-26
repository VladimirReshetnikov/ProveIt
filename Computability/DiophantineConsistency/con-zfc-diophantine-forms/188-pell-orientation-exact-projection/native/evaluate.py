#!/usr/bin/env python3
"""Evaluate a delivered circuit on positive integer witnesses, exactly or modulo m.

Usage: python3 evaluate.py q66_d118 witnesses.json --modulus 1000000007
Omit --modulus for the exact integer value (which may be very large).
This is an evaluator, not a search for a ZFC inconsistency witness.
"""
from pathlib import Path
import argparse,gzip,json

ROOT=Path(__file__).resolve().parent

def evaluate(graph,env,modulus=None):
    env=dict(env)
    for name,op,a,b in graph['source']:
        a=a if isinstance(a,int) else env[a]
        b=b if isinstance(b,int) else env[b]
        value=a+b if op=='+' else a-b if op=='-' else a*b
        env[name]=value if modulus is None else value%modulus
    return env[graph['output']]

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('circuit',choices=['q66_d118','q67_d94'])
    p.add_argument('witnesses',type=Path)
    p.add_argument('--modulus',type=int)
    args=p.parse_args()
    if args.modulus is not None and args.modulus<=1:
        p.error('modulus must exceed one')
    graph=json.loads((ROOT/'circuits'/(args.circuit+'.json')).read_text())
    supplied=json.loads(args.witnesses.read_text())
    if set(supplied)!=set(graph['witnesses']) or any(type(v)is not int or v<=0 for v in supplied.values()):
        p.error('supply exactly the fourteen named strictly positive integer witnesses')
    manifest=json.loads((ROOT/'coefficients.json').read_text())
    for port,rec in manifest['ports'].items():
        supplied[port]=int.from_bytes(gzip.decompress((ROOT/'coefficients'/rec['file']).read_bytes()),'big')
    out=evaluate(graph,supplied,args.modulus)
    # Python 3.11's decimal guard is not a mathematical limit.
    import sys
    if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
    print(out)

if __name__=='__main__':main()
