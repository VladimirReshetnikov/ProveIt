#!/usr/bin/env python3
"""Evaluate a delivered circuit with its actual fixed coefficient tuple.

Example:
  python3 evaluate.py circuits/positive12_product.json inputs.json --mod 1000003
No search for zeros is performed. Exact evaluation without --mod can produce
very large integers. Inputs are a JSON object keyed by witness names.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent

def coefficients():
    binding=json.loads((ROOT/'coefficients/COEFFICIENT_BINDING.json').read_text())
    aliases={'K':'K0','MF_source':'MF'}; result={}
    for entry in binding['materialization']['files']:
        raw=gzip.decompress((ROOT/'coefficients'/Path(entry['file']).name).read_bytes())
        if hashlib.sha256(raw).hexdigest()!=entry['sha256']:
            raise ValueError('coefficient hash mismatch: '+entry['port'])
        result[aliases.get(entry['port'],entry['port'])]=int.from_bytes(raw,'little')
    return result

def evaluate(packet,values,ports,modulus=None):
    env=dict(ports); env.update(values)
    def val(x): return x if isinstance(x,int) else env[x]
    for name,op,left,right in packet['source']:
        a,b=val(left),val(right)
        v=a+b if op=='+' else a-b if op=='-' else a*b if op=='*' else None
        if v is None: raise ValueError(op)
        env[name]=v if modulus is None else v%modulus
    return env[packet['output']]

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('circuit',type=Path);p.add_argument('inputs',type=Path)
    p.add_argument('--mod',type=int)
    a=p.parse_args();packet=json.loads(a.circuit.read_text());values=json.loads(a.inputs.read_text())
    if set(values)!=set(packet['witnesses']):raise ValueError('incorrect witness keys')
    if any(type(v) is not int for v in values.values()):raise ValueError('noninteger input')
    if packet['domain']=='strictly positive integers' and min(values.values())<1:raise ValueError('positive domain required')
    if packet['domain']=='nonnegative integers' and min(values.values())<0:raise ValueError('nonnegative domain required')
    if a.mod is not None and a.mod<2:raise ValueError('modulus must exceed one')
    value=evaluate(packet,values,coefficients(),a.mod)
    if a.mod is None:
        # Hexadecimal avoids a language-dependent decimal digit limit.
        print(hex(value))
    else:print(value)

if __name__=='__main__':main()
