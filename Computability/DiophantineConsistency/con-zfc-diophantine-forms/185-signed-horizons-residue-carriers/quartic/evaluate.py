#!/usr/bin/env python3
"""Evaluate one delivered fixed polynomial at an explicit integer tuple."""
import argparse,json,sys
from pathlib import Path
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('equation',type=Path)
    parser.add_argument('point',help='JSON file containing an integer list, or - for stdin')
    args=parser.parse_args()
    equation=json.loads(args.equation.read_text())
    point=json.load(sys.stdin) if args.point=='-' else json.loads(Path(args.point).read_text())
    if not isinstance(point,list) or any(type(x) is not int for x in point):
        raise ValueError('A point must be a JSON array of integers.')
    if len(point)!=len(equation['variables']):raise ValueError('Wrong dimension.')
    values=[]
    for row in equation['residuals']:
        total=0
        for coefficient,monomial in row['terms']:
            term=coefficient
            for i in monomial:term*=point[i]
            total+=term
        values.append(total)
    value=sum(x*x for x in values)
    print(json.dumps({'value':value,'is_zero':value==0,'nonzero_residuals':sum(x!=0 for x in values)}))

if __name__=='__main__':main()
