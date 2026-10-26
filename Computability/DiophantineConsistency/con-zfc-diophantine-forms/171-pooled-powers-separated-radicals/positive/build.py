#!/usr/bin/env python3
"""Compile85-gate inverse trace circuit from frozen87-gate trace JSON only."""
from pathlib import Path
from collections import Counter
import argparse, hashlib, json
ROOT=Path(__file__).resolve().parent

def construct():
    src=ROOT/'inherited_trace/equations/trace87_degree232.json'
    graph=json.loads(src.read_text());rows=[]
    for name,op,a,b in graph['source']:
        if name in ('v0','Rp1sq','Rp1sqm4','rank_cubic','v_rank_cubic'):continue
        if name=='V0k':a,b='XY','kY'
        if name=='q4s':rows.extend([['ksq','*','k','k'],['ksqm4','-','ksq',4],['inverse_cubic','*','V0k','ksqm4']])
        if name=='eclear':b='inverse_cubic'
        rows.append([name,op,a,b])
    if len(rows)!=85:raise ValueError('wrong operation count')
    graph.update(name='inverse_trace85_degree232', source=rows,operations=85,
        operation_breakdown=dict(Counter(r[1] for r in rows)),proof='PROOF.md',
        parent={'path':str(src.relative_to(ROOT)),'sha256':hashlib.sha256(src.read_bytes()).hexdigest()},
        generation='Inverse-Lucas cubic evaluated at k reuses ell=(XY)(kY); explicit unsquared Pell trace retained.',
        leaf_model='integer numerals and four whole integer ports; squares and scalar multiplications charged',
        status='Ordinary mathematical proof at retained native/refutation calibration; exact finite checks are separate; no new formal-kernel object.')
    graph['coefficient_binding']['path']='inherited_trace/coefficients/'
    graph['coefficient_binding']['endianness']='little'
    return graph

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
    graph=construct();path=ROOT/'equation_bV.json';data=json.dumps(graph,indent=2)+'\n'
    if a.check:
        if path.read_text()!=data:raise ValueError('rebuild mismatch')
    else:path.write_text(data)
    print(path.name, graph['operations'],graph['exact_degree'])
if __name__=='__main__':main()
