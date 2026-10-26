#!/usr/bin/env python3
"""Reconstruct the literal77-gate interpolation from frozen JSON."""
from pathlib import Path
from collections import Counter
import argparse,hashlib,json
ROOT=Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
    p=ROOT/'../inherited_trace/inherited/cofinal/provenance/centered/equation_q4_bV.json';g=json.loads(p.read_text());rows=[]
    for n,op,x,y in g['source']:
        if n=='Fsqr':n,op,x,y='trace_f','+','DpI2','Df'
        x='trace_f' if x=='Fsqr' else x;y='trace_f' if y=='Fsqr' else y
        rows.append([n,op,x,y])
    g.update(name='trace_q4_77_degree348',source=rows,operations=len(rows),operation_breakdown=dict(Counter(x[1] for x in rows)),exact_degree=348,chart='q4',proof='PROOF.md',parent={'path':'../inherited_trace/inherited/cofinal/provenance/centered/equation_q4_bV.json','sha256':hashlib.sha256(p.read_bytes()).hexdigest()},generation='Apply retained trace-linear map to retained q4-denominator graph; interpolation,not global priority claim.')
    g['coefficient_binding']['path']='../inherited_trace/coefficients/';g['coefficient_binding']['endianness']='little'
    data=json.dumps(g,indent=2)+'\n';out=ROOT/'equation.json'
    if a.check:
        if out.read_text()!=data:raise ValueError('graph reconstruction mismatch')
    else:out.write_text(data)
    print(g['operations'],g['exact_degree'])
if __name__=='__main__':main()
