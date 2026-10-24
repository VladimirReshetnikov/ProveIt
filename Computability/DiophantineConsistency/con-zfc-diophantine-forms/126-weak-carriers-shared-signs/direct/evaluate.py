#!/usr/bin/env python3
"""Evaluate both exact presentations of the selected quartic on a supplied tuple."""
import argparse,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
def evaluate(terms,z):
    total=0
    for c,mon in terms:
        t=c
        for i in mon:t*=z[i]
        total+=t
    return total
def main():
    ap=argparse.ArgumentParser();ap.add_argument('coordinates',type=Path);args=ap.parse_args()
    z=json.loads(args.coordinates.read_text())
    if not isinstance(z,list)or len(z)!=478 or any(type(x)is not int for x in z):raise ValueError('Expected a JSON array of exactly 478 integers.')
    eq=json.loads((HERE/'equation.json').read_text());expanded=json.loads((HERE/'expanded_polynomial.json').read_text())
    residuals=[evaluate(r['terms'],z)for r in eq['residuals']];value=sum(r*r for r in residuals)
    other=evaluate(expanded['terms'],z)
    if value!=other:raise ValueError('Presentations disagree')
    print(json.dumps({'value':value,'is_zero':value==0,'nonzero_residuals':sum(r!=0 for r in residuals),'presentations_agree':True}))
if __name__=='__main__':main()
