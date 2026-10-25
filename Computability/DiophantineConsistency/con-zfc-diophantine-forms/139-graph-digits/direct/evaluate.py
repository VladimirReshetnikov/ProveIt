#!/usr/bin/env python3
"""Exact evaluation at a supplied point; not a solvability decision procedure."""
from pathlib import Path
import argparse,json
ROOT=Path(__file__).resolve().parent
def evaluate(point,variant):
    if any(type(x)is not int for x in point):raise ValueError('every coordinate must be an integer')
    n=227 if variant=='natural227'else226
    if variant=='integer678':
        if len(point)!=678:raise ValueError('expected 678 integer coordinates')
        point=[point[3*i]**2+point[3*i+1]**2+point[3*i+2]*(point[3*i+2]+1) for i in range(226)]
    if len(point)!=n or any(x<0 for x in point):raise ValueError('wrong dimension or negative natural coordinate')
    eq=json.loads((ROOT/'equations'/('natural'+str(n))/'equation.json').read_text());value=0
    for r in eq['residuals']:
        row=0
        for c,m in r['terms']:
            term=c
            for i in m:term*=point[i]
            row+=term
        value+=row*row
    return value
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('point',type=Path);ap.add_argument('--variant',choices=['natural226','natural227','integer678'],default='natural226');a=ap.parse_args();print(evaluate(json.loads(a.point.read_text()),a.variant))
