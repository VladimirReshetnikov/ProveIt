#!/usr/bin/env python3
"""Compile the inverse-Lucas circuits from frozen JSON, without importing it."""
import argparse, hashlib, json
from collections import Counter
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def construct(weight):
    src=ROOT/'inherited_lucas'/f'equation_{weight}.json'
    graph=json.loads(src.read_text()); rows=[]
    for name,op,a,b in graph['source']:
        if name in ('v0','Rp1sq','Rp1sqm4','rank_cubic','v_rank_cubic'):
            continue
        if name=='V0k': a,b='XY','kY'
        if name=='q4s':
            rows.extend([['ksq','*','k','k'],['ksqm4','-','ksq',4],
                         ['inverse_cubic','*','V0k','ksqm4']])
        if name=='eclear': b='inverse_cubic'
        rows.append([name,op,a,b])
    ops=84 if weight=='V2' else 85
    if len(rows)!=ops: raise ValueError(('wrong count',weight,len(rows),ops))
    graph.update(name='inverse_lucas_q1_'+weight,source=rows,operations=ops,
        operation_breakdown=dict(Counter(r[1] for r in rows)),proof='PROOF.md',
        generation='Inverse-Lucas cubic reuses ell=v*k; projection precedes full-denominator recovery.',
        parent={'path':str(src.relative_to(ROOT)),'sha256':hashlib.sha256(src.read_bytes()).hexdigest()},
        status='Ordinary mathematical proof at the inherited calibrated native/refutation boundary; exact finite artifact checks are separate. No new formal-kernel object.')
    graph['coefficient_binding']['path']='inherited_lucas/parent/coefficients/'
    return graph

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
    for weight in ('V2','bV'):
        graph=construct(weight);path=ROOT/f'equation_{weight}.json'
        data=json.dumps(graph,indent=2)+'\n'
        if args.check:
            if path.read_text()!=data:raise ValueError('rebuild mismatch '+path.name)
        else:path.write_text(data)
        print(path.name,graph['operations'],graph['exact_degree'])
if __name__=='__main__':main()
