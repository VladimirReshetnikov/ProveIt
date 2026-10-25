#!/usr/bin/env python3
"""Evaluate one supplied polynomial at an integer tuple; no root search."""
from pathlib import Path
import argparse,json

def evaluate(program,coordinates,modulus=None):
    if len(coordinates)!=program['metrics']['variables'] or any(type(v) is not int for v in coordinates):raise ValueError('Wrong integer coordinate tuple')
    if modulus is not None and modulus<=1:raise ValueError('Modulus must exceed one')
    values=[]
    for node in program['nodes']:
        op=node[0]
        if op=='var':z=coordinates[node[1]]
        elif op=='const':z=node[1]
        elif op=='+':z=values[node[1]]+values[node[2]]
        elif op=='-':z=values[node[1]]-values[node[2]]
        elif op=='*':z=values[node[1]]*values[node[2]]
        else:raise ValueError('Invalid polynomial operation')
        values.append(z if modulus is None else z%modulus)
    return values[program['output']]

def main():
    pa=argparse.ArgumentParser(description=__doc__);pa.add_argument('equation',type=Path);pa.add_argument('coordinates',type=Path);pa.add_argument('--modulus',type=int);a=pa.parse_args()
    value=evaluate(json.loads(a.equation.read_text()),json.loads(a.coordinates.read_text()),a.modulus)
    print(json.dumps({'value_hex':hex(value),'is_zero':value==0,'modulus':a.modulus}))

if __name__=='__main__':main()
