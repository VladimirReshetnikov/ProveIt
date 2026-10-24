#!/usr/bin/env python3
"""Evaluate a literal DAG at supplied integers; no search is performed."""
import argparse,gzip,json
from pathlib import Path

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('packet',type=Path)
    p.add_argument('values',help='JSON object with exactly the declared witness values')
    p.add_argument('--mod',type=int,default=None)
    a=p.parse_args();packet=json.loads(a.packet.read_text());values=json.loads(a.values)
    if set(values)!=set(packet['witnesses']) or any(type(v) is not int for v in values.values()):
        raise ValueError('Supply exactly the declared integer witnesses')
    if a.mod is not None and a.mod<1:raise ValueError('Modulus must be positive')
    def reduce(x):return x if a.mod is None else x%a.mod
    values={k:reduce(v) for k,v in values.items()}
    for k,rel in packet['coefficient_binding']['ports'].items():
        raw=gzip.decompress((a.packet.resolve().parent/rel).read_bytes())
        values[k]=reduce(int.from_bytes(raw,'little'))
    for n,op,x,y in packet['source']:
        x=values[x] if isinstance(x,str) else x
        y=values[y] if isinstance(y,str) else y
        values[n]=reduce(x+y if op=='+' else x-y if op=='-' else x*y)
    print(json.dumps({'output':values[packet['output']],
        'residuals':[values[n] for n in packet['residuals']],'modulus':a.mod}))

if __name__=='__main__':main()
