#!/usr/bin/env python3
"""Evaluate a delivered fixed integer polynomial on one explicit tuple."""
import argparse,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--equation',default='integer112_degree24',help='Endpoint directory name')
    ap.add_argument('--values',required=True,help='JSON integer array file, or - for stdin')
    ap.add_argument('--modulus',type=int,help='Optional modulus greater than one')
    ap.add_argument('--residuals',action='store_true')
    a=ap.parse_args()
    name=Path(a.equation)
    if name.name!=str(name) or not (ROOT/'equations'/name/'circuit.json').is_file():raise ValueError('Unknown endpoint')
    c=json.loads((ROOT/'equations'/name/'circuit.json').read_text())
    xs=json.loads(sys.stdin.read() if a.values=='-' else Path(a.values).read_text())
    if not isinstance(xs,list) or len(xs)!=len(c['variables']) or any(type(x)is not int for x in xs):raise ValueError('Expected exactly '+str(len(c['variables']))+' integers')
    if a.modulus is not None and a.modulus<=1:raise ValueError('Modulus must exceed one')
    vs=[]
    for i,n in enumerate(c['nodes']):
        if n[0]=='var':v=xs[n[1]]
        elif n[0]=='const':v=n[1]
        else:
            if n[0] not in ('+','-','*') or not all(type(k)is int and 0<=k<i for k in n[1:]):raise ValueError('Malformed circuit')
            u,w=vs[n[1]],vs[n[2]];v=u+w if n[0]=='+' else u-w if n[0]=='-' else u*w
        vs.append(v if a.modulus is None else v%a.modulus)
    out={'equation':a.equation,'value':vs[c['output']],'domain':'unrestricted integers'}
    if a.modulus is not None:out['modulus']=a.modulus
    if a.residuals:out['residuals']=[vs[i] for i in c['residual_outputs']]
    print(json.dumps(out))
if __name__=='__main__':main()
