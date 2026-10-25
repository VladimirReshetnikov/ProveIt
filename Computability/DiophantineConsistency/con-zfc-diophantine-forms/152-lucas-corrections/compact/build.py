#!/usr/bin/env python3
"""Second-order Lucas-index correction for a q-linear positive scale.

Input is frozen parent JSON only.  No upstream executable is imported.
"""
from pathlib import Path
import copy, hashlib, json
from collections import Counter

ROOT=Path(__file__).resolve().parent

def construct(weight):
    src=ROOT/'parent'/f'equation_XY_{weight}.json'
    graph=json.loads(src.read_text())
    rows=[]
    for name,op,a,b in graph['source']:
        if name=='q3':
            continue
        if name=='Y':
            a='q'
        if name=='V0k':
            a,b='v0','k'
        if name=='e':
            continue
        if name=='kR':
            rows.extend([
                ['Rp1','+','R',1],
                ['e','-','k','Rp1'],
                ['Rp1sq','*','Rp1','Rp1'],
                ['Rp1sqm4','-','Rp1sq',4],
                ['rank_cubic','*','Rp1','Rp1sqm4'],
                ['v_rank_cubic','*','v0','rank_cubic'],
                ['q4s','*','q4','s'],
                ['e_sigma','-','e','q4s'],
                ['six_e_sigma','*',6,'e_sigma'],
                ['eclear','-','six_e_sigma','v_rank_cubic']
            ])
            continue
        if name in ('P1mu2','mu2inner'):
            a='sixq6' if a=='XY' else a
            b='sixq6' if b=='XY' else b
        if name=='P1e':
            b='eclear'
        rows.append([name,op,a,b])
        if name=='q2':
            rows.extend([
                ['q4','*','q2','q2'],
                ['q6','*','q4','q2'],
                ['sixq6','*',6,'q6']
            ])
        if name=='XY':
            rows.append(['v0','*','XY','Y'])
    degree=410 if weight=='V2' else 304
    graph.update(
        name=f'second_order_lucas_q1_{weight}', source=rows,
        operations=len(rows), operation_breakdown=dict(Counter(r[1] for r in rows)),
        exact_degree=degree, denominator='6q6',
        proof='PROOF.md',
        generation='Y=q*s; second-order Lucas correction; denominator 6q^6; delayed recovery q^2|s.',
        parent={'path':str(src.relative_to(ROOT)), 'sha256':hashlib.sha256(src.read_bytes()).hexdigest()},
        status='Ordinary arithmetic proof independently reviewed, composed with the identified inherited native/refutation calibration; exact finite artifact checks passed. No new end-to-end formal proof object.'
    )
    graph['coefficient_binding']['path']='parent/coefficients/'
    return graph

def main():
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
    receipts=[]
    for weight in ('V2','bV'):
        g=construct(weight)
        p=ROOT/f'equation_{weight}.json'
        text=json.dumps(g,indent=2)+'\n'
        if args.check:
            if p.read_text()!=text:raise ValueError('Rebuild mismatch '+p.name)
        else:p.write_text(text)
        receipts.append({'path':p.name,'operations':g['operations'],'exact_degree':g['exact_degree']})
    print(json.dumps(receipts,indent=2))

if __name__=='__main__':main()
