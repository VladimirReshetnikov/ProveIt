#!/usr/bin/env python3
"""Evaluate the exact quartic on a supplied integer tuple; no root search."""
import argparse
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parent

def evaluate(equation, point):
    n=len(equation['variables'])
    if type(point) is not list or len(point)!=n or any(type(x) is not int for x in point):
        raise ValueError(f'Expected a JSON array of exactly {n} integers; booleans and floats are rejected.')
    values=[]
    for row in equation['residuals']:
        value=0
        for coefficient,monomial in row['terms']:
            term=coefficient
            for i in monomial:term*=point[i]
            value+=term
        values.append(value)
    return {'variables':n,'residuals':len(values),
            'polynomial_value':sum(v*v for v in values),
            'is_zero':all(v==0 for v in values),
            'nonzero_residuals':sum(v!=0 for v in values),
            'maximum_absolute_residual':max(map(abs,values))}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('point',help='JSON file with the coordinate array, or - for standard input')
    p.add_argument('--equation',type=Path,default=ROOT/'equations/principal/equation.json')
    a=p.parse_args()
    point=json.loads(sys.stdin.read() if a.point=='-' else Path(a.point).read_text())
    eq=json.loads(a.equation.read_text())
    print(json.dumps(evaluate(eq,point),indent=2))

if __name__=='__main__':main()
