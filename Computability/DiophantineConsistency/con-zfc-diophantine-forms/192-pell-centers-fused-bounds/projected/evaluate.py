#!/usr/bin/env python3
"""Evaluate the literal integer polynomial at a supplied tuple; no search."""
from pathlib import Path
import argparse,json,sys

ROOT=Path(__file__).resolve().parent
def main():
    p=argparse.ArgumentParser()
    p.add_argument('--profile',default='integer82_degree16964_linear',choices=['integer82_degree16964_linear','integer81_degree2097732_linear','integer106_degree32_linear'])
    p.add_argument('--variables',action='store_true')
    g=p.add_mutually_exclusive_group();g.add_argument('--tuple',type=Path);g.add_argument('--zero',action='store_true')
    p.add_argument('--modulus',type=int);p.add_argument('--residuals',action='store_true')
    a=p.parse_args();d=json.loads((ROOT/'equations'/(a.profile+'.json')).read_text())
    if a.variables:
        print(json.dumps(d['variables'],indent=2));return
    if a.modulus is not None and a.modulus<2:p.error('modulus must be at least 2')
    if a.zero:xs=[0]*len(d['variables'])
    elif a.tuple:xs=json.loads(a.tuple.read_text())
    else:p.error('supply --tuple, --zero, or --variables')
    if not isinstance(xs,list) or len(xs)!=len(d['variables']) or any(type(x) is not int for x in xs):
        p.error('tuple must contain exactly the declared number of integers, excluding booleans')
    values=[]
    for n in d['nodes']:
        op=n[0]
        if op=='var':v=xs[n[1]]
        elif op=='const':v=n[1]
        elif op=='+':v=values[n[1]]+values[n[2]]
        elif op=='-':v=values[n[1]]-values[n[2]]
        elif op=='*':v=values[n[1]]*values[n[2]]
        else:raise ValueError('Unknown instruction')
        values.append(v if a.modulus is None else v%a.modulus)
    if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
    out={'profile':a.profile,'modulus':a.modulus,'value':values[d['output']]}
    if a.residuals:out['residuals']=[values[r] for r in d['residual_roots']]
    print(json.dumps(out))
if __name__=='__main__':main()
