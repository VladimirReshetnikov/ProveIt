#!/usr/bin/env python3
"""Evaluate a literal natural-domain sum-of-squares equation at one point."""
from pathlib import Path
import argparse,json

HERE=Path(__file__).resolve().parent

def evaluate(equation,point):
    if not isinstance(point,list) or len(point)!=len(equation['variables']):
        raise ValueError('point has the wrong dimension')
    if not all(type(v) is int and v>=0 for v in point):
        raise ValueError('every coordinate must be a nonnegative integer')
    values=[]
    for row in equation['residuals']:
        total=0
        for c,m in row['terms']:
            term=c
            for i in m:term*=point[i]
            total+=term
        values.append(total)
    return {'polynomial_value':sum(v*v for v in values),
            'is_zero':all(v==0 for v in values),'residual_values':values}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('point',type=Path)
    p.add_argument('--equation',type=Path,
        default=HERE/'equations/principal241/natural/equation.json')
    a=p.parse_args()
    print(json.dumps(evaluate(json.loads(a.equation.read_text()),
                              json.loads(a.point.read_text())),indent=2))
