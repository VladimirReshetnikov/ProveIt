#!/usr/bin/env python3
"""Evaluate a supplied tuple; no root search is performed."""
from pathlib import Path
import argparse,hashlib,json,sys
from check_independent import load_coefficients

ROOT=Path(__file__).resolve().parent

def evaluate(graph,inputs,modulus=None):
    names=graph['witnesses']
    if len(inputs)!=len(names) or any(type(x) is not int or x<=0 for x in inputs):
        raise ValueError('Supply exactly ten strictly positive integers.')
    if modulus is not None and modulus<2:raise ValueError('Modulus must be at least 2.')
    values=load_coefficients(graph)
    values.update(zip(names,inputs))
    if modulus:values={k:v%modulus for k,v in values.items()}
    for name,op,left,right in graph['source']:
        a=left if isinstance(left,int) else values[left]
        b=right if isinstance(right,int) else values[right]
        out=a+b if op=='+' else a-b if op=='-' else a*b
        values[name]=out%modulus if modulus else out
    return values[graph['output']]

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--equation',choices=['190','202'],default='190')
    parser.add_argument('--values',type=Path)
    parser.add_argument('--modulus',type=int)
    parser.add_argument('--variables',action='store_true')
    parser.add_argument('--value',action='store_true',help='Also print the full exact integer value.')
    args=parser.parse_args()
    filename='whole190.json' if args.equation=='190' else 'quotient202.json'
    graph=json.loads((ROOT/filename).read_text())
    if args.variables:print(json.dumps(graph['witnesses']))
    if args.values:
        inputs=json.loads(args.values.read_text())
        if not isinstance(inputs,list):parser.error('The tuple file must contain a JSON array.')
        try:value=evaluate(graph,inputs,args.modulus)
        except ValueError as exc:parser.error(str(exc))
        if args.modulus:
            result={'equation':filename,'modulus':args.modulus,'modular_value':value}
        else:
            mag=abs(value);raw=mag.to_bytes((mag.bit_length()+7)//8 or 1,'big')
            result={'equation':filename,'is_zero':value==0,'sign':(value>0)-(value<0),
                    'magnitude_bits':mag.bit_length(),'magnitude_sha256':hashlib.sha256(raw).hexdigest()}
            if args.value:
                if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
                result['value']=value
        print(json.dumps(result,indent=2))
    elif not args.variables:parser.error('Choose --variables or provide --values tuple.json.')
