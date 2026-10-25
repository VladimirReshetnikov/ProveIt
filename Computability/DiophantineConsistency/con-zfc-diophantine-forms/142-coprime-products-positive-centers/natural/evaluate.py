#!/usr/bin/env python3
"""Exact evaluation of a supplied natural tuple, never a solvability search."""
from pathlib import Path
import argparse
import json

ROOT=Path(__file__).resolve().parent


def evaluate(values,size):
    if len(values)!=size or any(type(value) is not int or value<0 for value in values):
        raise ValueError(f'Expected {size} nonnegative integers')
    equation=json.loads((ROOT/'equations'/('natural'+str(size))/'equation.json').read_text())
    residual_values=[]
    for row in equation['residuals']:
        value=0
        for coefficient,monomial in row['terms']:
            term=coefficient
            for index in monomial:
                term*=values[index]
            value+=term
        residual_values.append(value)
    return {'polynomial_value':sum(value*value for value in residual_values),
            'residual_values':residual_values}


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('coordinates',type=Path)
    parser.add_argument('--variables',type=int,choices=[221,222],default=221)
    args=parser.parse_args()
    print(json.dumps(evaluate(json.loads(args.coordinates.read_text()),args.variables),indent=2))
