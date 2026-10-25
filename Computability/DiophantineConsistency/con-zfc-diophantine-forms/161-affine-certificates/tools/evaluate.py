#!/usr/bin/env python3
"""Evaluate a supplied complete sum-of-squares equation at an integer tuple.

Example: python3 tools/evaluate.py equations/balanced239/equation.json values.json
The second file must contain a JSON array of exactly the advertised length.
"""
import argparse
import json
from pathlib import Path

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('equation',type=Path);p.add_argument('values',type=Path)
    a=p.parse_args();e=json.loads(a.equation.read_text());x=json.loads(a.values.read_text())
    if len(x)!=len(e['variables']) or any(type(v) is not int for v in x):
        raise ValueError('Expected an integer tuple of the exact coordinate length')
    residuals=[]
    for row in e['residuals']:
        value=0
        for c,mon in row['terms']:
            term=c
            for i in mon:term*=x[i]
            value+=term
        residuals.append(value)
    print(json.dumps({'polynomial_value':sum(v*v for v in residuals),'zero':all(v==0 for v in residuals),'residuals':residuals}))

if __name__=='__main__':main()
