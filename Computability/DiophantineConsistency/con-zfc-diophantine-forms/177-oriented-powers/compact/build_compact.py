#!/usr/bin/env python3
"""Build the three ten-positive root-centering circuits from a frozen DAG."""
from pathlib import Path
from collections import Counter
import copy, hashlib, json, argparse

ROOT = Path(__file__).resolve().parent
PARENT = ROOT/'164-unsquared-factors-linear-selectors/positive/equation_bV.json'

def construct(weight='b2', centered=False):
    g=json.loads(PARENT.read_text())
    rows=[]
    for name,op,a,b in g['source']:
        if name=='Fsqr':
            rows.append(['trace_f','+','DpI2','Df']); continue
        a='trace_f' if a=='Fsqr' else a
        b='trace_f' if b=='Fsqr' else b
        if name=='L' and weight=='b2': b='cTR'
        if name=='Z2' and centered:
            rows.extend([
                ['A','+','Am1',1],
                ['root_center','*','A','UE'],
                ['center_V','*','root_center','V'],
                ['scaled_center','*','Mtot','center_V'],
                ['Zshift','-','Znum','scaled_center']])
            a=b='Zshift'
        rows.append([name,op,a,b])
    name=('centered224' if centered else 'inverse_trace232_'+weight)
    g.update(name=name,source=rows,operations=len(rows),
        operation_breakdown=dict(Counter(r[1] for r in rows)),
        exact_degree=224 if centered else 232,transport_weight=weight,
        proof='PROOF_COMPACT.md',
        parent={'path':str(PARENT.relative_to(ROOT)),
                'sha256':hashlib.sha256(PARENT.read_bytes()).hexdigest()},
        status='Ordinary mathematical proof relative to the pinned native/refutation calibration, with separate exact finite checks.',
        generation='Unsquared doubled trace; inverse Lucas correction; optional square transport and polynomial root center.')
    g['coefficient_binding']['path']='coefficients/'
    return g

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
    target=ROOT/'compact_equations';target.mkdir(exist_ok=True)
    for weight,centered in [('bV',False),('b2',False),('b2',True)]:
        g=construct(weight,centered);p=target/(g['name']+'.json')
        data=json.dumps(g,indent=2)+'\n'
        if args.check:
            if p.read_text()!=data: raise ValueError('Rebuild differs: '+str(p))
        else:p.write_text(data)
        print(g['name'],g['operations'],g['exact_degree'])

if __name__=='__main__': main()
