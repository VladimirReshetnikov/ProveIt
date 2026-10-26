#!/usr/bin/env python3
"""Byte-reproducible centered inverse-Lucas graph; no rational leaves."""
from pathlib import Path
from collections import Counter
import argparse, hashlib, json
ROOT=Path(__file__).resolve().parent

def construct():
    src=ROOT/'parent/equation_bV.json'
    graph=json.loads(src.read_text());rows=[]
    for name,op,a,b in graph['source']:
        if name=='L':
            rows.extend([['A','+','Am1',1],['g0','*','A','UE'],['bB','*','cTR','Bt'],['bB_g0','+','bB','g0']]);continue
        if name=='LBt': a,b='V','bB_g0'
        rows.append([name,op,a,b])
    if len(rows)!=88:raise ValueError('wrong operation count')
    graph.update(name='centered_inverse_trace88_degree224',source=rows,operations=88,
        exact_degree=224,operation_breakdown=dict(Counter(r[1] for r in rows)),proof='PROOF.md',
        parent={'path':str(src.relative_to(ROOT)),'sha256':hashlib.sha256(src.read_bytes()).hexdigest()},
        generation='Center the rational carrier at AUEV; factor bVB+AUEV as V(bB+AUE).',
        leaf_model='integer numerals and four whole integer ports; squares and scalar multiplications charged',
        status='Ordinary mathematical proof at retained native/refutation calibration; exact finite checks are separate; no new formal-kernel object.')
    graph['coefficient_binding']['path']='parent/inherited_trace/coefficients/'
    graph['coefficient_binding']['endianness']='little'
    return graph

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
    graph=construct();path=ROOT/'equation_bV.json';data=json.dumps(graph,indent=2)+'\n'
    if a.check:
        if path.read_text()!=data:raise ValueError('rebuild mismatch')
    else:path.write_text(data)
    print(path.name,graph['operations'],graph['exact_degree'])
if __name__=='__main__':main()
