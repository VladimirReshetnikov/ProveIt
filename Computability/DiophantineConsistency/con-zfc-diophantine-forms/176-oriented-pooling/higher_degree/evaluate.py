#!/usr/bin/env python3
"""Evaluate one emitted integer polynomial at an explicitly supplied tuple."""
import argparse,json,sys
from pathlib import Path

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('equation',type=Path)
    parser.add_argument('tuple',help='JSON array filename, or - for stdin')
    parser.add_argument('--residuals',action='store_true')
    args=parser.parse_args()
    program=json.loads(args.equation.read_text())
    values=json.load(sys.stdin) if args.tuple=='-' else json.loads(Path(args.tuple).read_text())
    if type(values) is not list or len(values)!=len(program['variables']) or any(type(x) is not int for x in values):
        parser.error('Expected exactly '+str(len(program['variables']))+' integer coordinates')
    cache=[]
    for node in program['nodes']:
        op=node[0]
        if op=='var':v=values[node[1]]
        elif op=='const':v=node[1]
        elif op=='+':v=cache[node[1]]+cache[node[2]]
        elif op=='-':v=cache[node[1]]-cache[node[2]]
        elif op=='*':v=cache[node[1]]*cache[node[2]]
        else:raise ValueError('Unsupported circuit operation')
        cache.append(v)
    if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
    result={'value':cache[program['output']]}
    if args.residuals:result['residuals']=[cache[i] for i in program['residual_roots']]
    print(json.dumps(result))
if __name__=='__main__':main()
