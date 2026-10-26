#!/usr/bin/env python3
"""Evaluate a supplied integer tuple; this is not a consistency/root search."""
import argparse,json,sys
from pathlib import Path

ROOT=Path(__file__).resolve().parent
def main():
    ap=argparse.ArgumentParser();ap.add_argument('profile',type=int);ap.add_argument('tuple',type=Path);ap.add_argument('--modulus',type=int);ap.add_argument('--residuals',action='store_true');ap.add_argument('--restore227',action='store_true');ap.add_argument('--factored',action='store_true');a=ap.parse_args()
    if a.factored and a.profile!=83:raise ValueError('the factored evaluator is supplied for profile 83')
    graph_path=ROOT/'factored83/circuit.json' if a.factored else ROOT/f'P{a.profile}/circuit.json'
    g=json.loads(graph_path.read_text());point=json.loads(a.tuple.read_text())
    if not isinstance(point,list) or len(point)!=a.profile or any(type(v) is not int for v in point):raise ValueError('tuple must be a JSON list of exactly the declared number of integers')
    if a.modulus is not None and a.modulus<=0:raise ValueError('modulus must be positive')
    values=[]
    for n in g['nodes']:
        if n[0]=='input':v=point[n[1]]
        elif n[0]=='const':v=n[1]
        elif n[0]=='add':v=values[n[1]]+values[n[2]]
        elif n[0]=='mul':v=values[n[1]]*values[n[2]]
        else:raise ValueError('unknown graph operation')
        values.append(v if a.modulus is None else v%a.modulus)
    out={'value':values[g['output']]}
    if a.modulus is not None:out['modulus']=a.modulus
    if a.residuals:out['residuals']=[values[r] for r in g['residual_roots']]
    if a.restore227:out['source227']=[values[r] for r in g['source_coordinate_roots']]
    if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
