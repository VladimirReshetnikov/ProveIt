#!/usr/bin/env python3
"""Emit the XY-carrier circuits without running any upstream code."""
from __future__ import annotations
import argparse
from collections import Counter
from copy import deepcopy
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent

def compile_variant(parent, unshift=True):
    result=deepcopy(parent)
    rows=[]
    for name, op, a, b in parent['source']:
        if name == 'Xp1':
            rows.append(['D','*','X','Y'])
            continue
        if name == 'Y2' or unshift and name == 'Tp':
            continue
        if name == 'Am1':
            op,a,b='+','D','Y'
        elif name == 'V0':
            op,a,b='*','D','Y'
        else:
            a='D' if a=='Y2' else ('T' if unshift and a=='Tp' else a)
            b='D' if b=='Y2' else ('T' if unshift and b=='Tp' else b)
        rows.append([name,op,a,b])
    result['name']='xy_carrier_'+('V2' if parent['transport_weight']=='V^2' else 'bV')+('_unshifted' if unshift else '_shifted')
    result['source']=rows
    result['operations']=len(rows)
    result['operation_breakdown']=dict(sorted(Counter(r[1] for r in rows).items()))
    result['exact_degree']=626 if parent['transport_weight']=='V^2' else 464
    result['carrier_denominator_factor']='X*Y'
    result['Y_q_exponent']=3
    result['retain_fraction_s_over_q']=False
    result['auxiliary_T_shift']=not unshift
    result['parent']='upstream/equation'+('78' if parent['transport_weight']=='V^2' else '79')+'.json'
    result['parent_sha256']=hashlib.sha256((ROOT/result['parent']).read_bytes()).hexdigest()
    result['proof']='PROOF.md'
    return result

def compile_partial(parent):
    result=compile_variant(parent,True)
    rows=[]
    for name,op,a,b in result['source']:
        if name=='q3':continue
        if name=='Y':a='q2'
        elif name=='P1mu2':b='D1'
        elif name=='mu2inner':a='D1'
        elif name=='P1e':
            rows += [['sE0','*','s','E0'],['eclear','-','e','sE0']]
            b='eclear'
        rows.append([name,op,a,b])
        if name=='Y':rows += [['E0','*','q2','q2'],['D1','*','q','E0']]
    result['name']='partial_q2_'+('V2' if parent['transport_weight']=='V^2' else 'bV')
    result['source']=rows
    result['operations']=len(rows)
    result['operation_breakdown']=dict(sorted(Counter(r[1] for r in rows).items()))
    result['exact_degree']=516 if parent['transport_weight']=='V^2' else 382
    result['carrier_denominator_factor']='q^5'
    result['Y_q_exponent']=2
    result['retain_fraction_s_over_q']=True
    result['proof']='PARTIAL_Q2_PROOF.md'
    return result

def encode(x): return json.dumps(x,indent=2,ensure_ascii=False)+'\n'

def main():
    p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
    summaries=[]
    for num in [78,79]:
        parent=json.loads((ROOT/'upstream'/f'equation{num}.json').read_text())
        for unshift in [False,True]:
            d=compile_variant(parent,unshift)
            name=f"equation_{d['operations']}_{d['exact_degree']}"+('' if unshift else '_shifted')+'.json'
            target=ROOT/name;payload=encode(d)
            if a.check:
                if not target.exists() or target.read_text()!=payload: raise ValueError('Rebuild differs: '+name)
            else: target.write_text(payload)
            summaries.append({k:d[k] for k in ['name','operations','operation_breakdown','exact_degree']})
        d=compile_partial(parent)
        name=f"equation_{d['operations']}_{d['exact_degree']}_partial.json"
        target=ROOT/name;payload=encode(d)
        if a.check:
            if not target.exists() or target.read_text()!=payload:raise ValueError('Rebuild differs: '+name)
        else:target.write_text(payload)
        summaries.append({k:d[k] for k in ['name','operations','operation_breakdown','exact_degree']})
    print(json.dumps(summaries,indent=2))

if __name__=='__main__': main()
