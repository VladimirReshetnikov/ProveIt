#!/usr/bin/env python3
"""Produce two literal positive Diophantine circuits from immutable parents.

Only JSON data are read from the parents; no parent executable is run.
"""
from pathlib import Path
from collections import Counter
import argparse, hashlib, json

ROOT = Path(__file__).resolve().parent

def construct(mode):
    path = ROOT / ('parent_q1_bv.json' if mode == 'plain' else 'upstream_lucas/equation_bV.json')
    data = json.loads(path.read_text())
    rows=[]
    for name,op,a,b in data['source']:
        # The old Y=q*s is now lambda*Y, lambda=q, while actual Y=s.
        if name=='Y': name='qY'
        if a=='Y': a='qY'
        if b=='Y': b='qY'
        if name=='kY': b='s'
        if name=='D' and mode=='plain':
            rows.append(['q6',op,a,b])
            a,b='q6','q'
        if name=='sixq6' and mode=='corrected':
            rows.append(['q7','*','q6','q'])
            name='sixq7'; b='q7'
        if a=='sixq6': a='sixq7'
        if b=='sixq6': b='sixq7'
        if name=='V0k' and mode=='plain':
            # v*k = (X*qY)*(q*kY), with kY=k*s.
            rows.append(['qkY','*','q','kY'])
            b='qkY'
        if name=='cT':
            rows.append(['Tshift','+','T','alpha'])
            b='Tshift'
        rows.append([name,op,a,b])
    data.update(name='free_quotient_scale_'+mode, source=rows,
        operations=len(rows), operation_breakdown=dict(sorted(Counter(r[1] for r in rows).items())),
        exact_degree=312 if mode=='plain' else 278,
        parent={'path':str(path.relative_to(ROOT)),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()},
        normalization='lambda=q; Y=s; positive auxiliary shift T+alpha',
        denominator='q^7' if mode=='plain' else '6*q^7',
        proof='PROOF.md', status='Ordinary theorem relative to retained, explicitly identified native/refutation calibration. No new proof-assistant certificate.',
        generation='Move q from the quotient Y into the Pell scale; recover the full denominator after the exponential projection.')
    data['coefficient_binding']['path']='upstream_lucas/parent/coefficients/'
    expected=83 if mode=='plain' else 89
    if len(rows)!=expected:raise ValueError((mode,len(rows),expected))
    return data

def main():
    p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');args=p.parse_args()
    out=[]
    for mode in ['plain','corrected']:
        data=construct(mode)
        name=f"equation_{data['operations']}_degree{data['exact_degree']}.json"
        encoded=json.dumps(data,indent=2)+'\n'
        if args.check:
            if (ROOT/name).read_text()!=encoded:raise ValueError('Mismatch '+name)
        else:(ROOT/name).write_text(encoded)
        out.append({'file':name,'operations':data['operations'],'degree':data['exact_degree']})
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
