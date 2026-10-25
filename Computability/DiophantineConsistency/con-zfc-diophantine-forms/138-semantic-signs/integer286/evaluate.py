#!/usr/bin/env python3
"""Evaluate a specified integer point exactly; this is not a solver."""
from pathlib import Path
import argparse,json,sys
ROOT=Path(__file__).resolve().parent
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
def main():
    p=argparse.ArgumentParser();p.add_argument('point',type=Path);p.add_argument('--companion',action='store_true');a=p.parse_args()
    folder='generated' if a.companion else 'principal'
    equation=json.loads((ROOT/folder/'centered/equation.json').read_text())
    values=json.loads(a.point.read_text())
    if not isinstance(values,list) or len(values)!=len(equation['variables']) or any(type(x) is not int for x in values):
        raise ValueError('Expected an array of exactly '+str(len(equation['variables']))+' integers.')
    residuals=[]
    for row in equation['residuals']:
        value=0
        for coefficient,monomial in row['terms']:
            term=coefficient
            for i in monomial:term*=values[i]
            value+=term
        residuals.append(value)
    print(json.dumps({'polynomial_value':sum(r*r for r in residuals),'zero':all(r==0 for r in residuals),'nonzero_residuals':[i for i,r in enumerate(residuals) if r!=0]},indent=2))
if __name__=='__main__':main()
