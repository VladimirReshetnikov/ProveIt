#!/usr/bin/env python3
"""Evaluate a supplied tuple. This is not a root search."""
from pathlib import Path
import argparse,hashlib,json

HERE=Path(__file__).resolve().parent
def main():
    a=argparse.ArgumentParser(description=__doc__)
    a.add_argument('tuple',type=Path)
    a.add_argument('--profile',choices=['positive13_square','positive13_oriented','integer39_square','integer39_oriented'],default='integer39_square')
    a.add_argument('--modulus',type=int)
    args=a.parse_args()
    g=json.loads((HERE/(args.profile+'.json')).read_text());x=json.loads(args.tuple.read_text())
    if not isinstance(x,list) or len(x)!=len(g['witnesses']) or any(type(v) is not int for v in x):raise ValueError('Wrong tuple length or noninteger entry')
    if g['witness_domain']=='strictly positive integers' and any(v<=0 for v in x):raise ValueError('All entries must be positive')
    mod=args.modulus
    if mod is not None and mod<2:raise ValueError('Modulus must be at least two')
    env=dict(zip(g['witnesses'],x))
    for n,f in g['coefficient_binding']['ports'].items():env[n]=int.from_bytes((HERE/'coefficients'/f).read_bytes(),'big')
    if mod:env={n:v%mod for n,v in env.items()}
    for name,op,l,r in g['source']:
        aa=l if type(l) is int else env[l];bb=r if type(r) is int else env[r]
        v=aa+bb if op=='+' else aa-bb if op=='-' else aa*bb
        env[name]=v%mod if mod else v
    v=env[g['output']]
    out={'profile':args.profile,'domain':g['witness_domain'],'zero':v==0,'modulus':mod}
    if mod:out['residue']=v;out['scope']='A modular zero need not be an integer zero.'
    else:
        raw=abs(v).to_bytes((abs(v).bit_length()+7)//8,'big')
        out.update(sign=(v>0)-(v<0),magnitude_bits=abs(v).bit_length(),magnitude_sha256=hashlib.sha256(raw).hexdigest())
    print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
