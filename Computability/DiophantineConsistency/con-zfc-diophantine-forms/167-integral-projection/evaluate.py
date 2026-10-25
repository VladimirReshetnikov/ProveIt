#!/usr/bin/env python3
"""Evaluate either fixed quartic on an explicitly supplied integer tuple."""
import argparse,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--variant',choices=['218','220'],default='220');ap.add_argument('--values',required=True,help='JSON array file, or - for stdin');ap.add_argument('--residuals',action='store_true');args=ap.parse_args()
    root=ROOT if args.variant=='218' else ROOT/'variants/220'
    eq=json.loads((root/'equation/equation.json').read_text())
    vals=json.load(sys.stdin) if args.values=='-' else json.loads(Path(args.values).read_text())
    if type(vals) is not list or len(vals)!=len(eq['variables']) or any(type(v) is not int for v in vals):raise ValueError('Expected exactly '+str(len(eq['variables']))+' unrestricted integers')
    residual=[]
    for row in eq['residuals']:
        value=0
        for c,mon in row['terms']:
            for i in mon:c*=vals[i]
            value+=c
        residual.append(value)
    out={'variant':args.variant,'value':sum(v*v for v in residual)}
    if args.residuals:out['residuals']=residual
    print(json.dumps(out))
if __name__=='__main__':main()
