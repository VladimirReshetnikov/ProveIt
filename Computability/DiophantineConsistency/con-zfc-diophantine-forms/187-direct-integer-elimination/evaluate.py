#!/usr/bin/env python3
"""Evaluate a complete polynomial circuit; this is not a root search."""
from pathlib import Path
import argparse,json,sys
ROOT=Path(__file__).resolve().parent

def run(program,values,modulus=None):
    if len(values)!=len(program['variables']) or any(type(v) is not int for v in values):
        raise ValueError('Expected exactly the declared number of integer inputs')
    if modulus is not None and (type(modulus) is not int or modulus<2):
        raise ValueError('Modulus must be an integer at least two')
    evaluated=[]
    for i,node in enumerate(program['nodes']):
        op=node[0]
        if op=='var':value=values[node[1]]
        elif op=='const':value=node[1]
        else:
            a,b=(evaluated[k] for k in node[1:])
            if op=='+':value=a+b
            elif op=='-':value=a-b
            elif op=='*':value=a*b
            else:raise ValueError(('Unknown operation',op))
        if modulus is not None:value%=modulus
        evaluated.append(value)
    return evaluated[program['output']],[evaluated[r] for r in program['residual_roots']]

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--profile',default='integer85_degree16964')
    p.add_argument('--variables',action='store_true')
    g=p.add_mutually_exclusive_group();g.add_argument('--tuple',type=Path);g.add_argument('--zero',action='store_true')
    p.add_argument('--modulus',type=int);p.add_argument('--residuals',action='store_true');a=p.parse_args()
    path=ROOT/'equations'/(a.profile+'.json')
    if path.parent.resolve()!=(ROOT/'equations').resolve():p.error('Profile must be a basename')
    program=json.loads(path.read_text())
    if a.variables:
        print(json.dumps(program['variables'],indent=2));return
    if a.tuple:values=json.loads(a.tuple.read_text())
    elif a.zero:values=[0]*len(program['variables'])
    else:p.error('Use --variables, --tuple, or --zero')
    value,residuals=run(program,values,a.modulus)
    if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
    result={'profile':a.profile,'modulus':a.modulus,'value':value}
    if a.residuals:result['residuals']=residuals
    print(json.dumps(result))
if __name__=='__main__':main()
