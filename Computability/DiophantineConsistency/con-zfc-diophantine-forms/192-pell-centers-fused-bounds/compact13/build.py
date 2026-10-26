#!/usr/bin/env python3
"""Build a second Pell carrier from the pinned first-carrier graph."""
from pathlib import Path
from collections import Counter
import hashlib,json

HERE=Path(__file__).resolve().parent
PARENT=HERE/'parent65.json'

def build(weight='square'):
    p=json.loads(PARENT.read_text())
    rows=[]
    removed={'transport_partial','zqm','Nt','product3'}
    for name,op,left,right in p['source']:
        if name in removed:continue
        if name=='normalized_S':
            rows.append(['hi','*','qm','i'])
            left='hi'
        if name=='y2':
            if weight=='oriented':
                rows.append(['L','*','cTminusR','V'])
                weightname='L'
            else:weightname='V2'
            rows.extend([
                ['LB','*',weightname,'B'],
                ['mLB','-','m','LB'],
                ['h_mLB','*','qm','mLB'],
                ['carrier','-','h_mLB','B'],
                ['four_carrier','*',4,'carrier'],
                ['y','+','four_carrier',1],
            ])
        if name=='product4':left='product1'
        rows.append([name,op,left,right])
        if name=='transport':rows.append(['B','-','transport','F'])
    out={k:p[k] for k in ['fixed_numerals','coefficient_binding','witness_domain','schema','output']}
    out.update(name='double_pell_carrier_'+weight,
        witnesses=[('m' if v=='y' else v) for v in p['witnesses'] if v!='z'],
        source=rows,operations=len(rows),operation_counts=dict(sorted(Counter(r[1] for r in rows).items())),
        exact_degree=174 if weight=='square' else 170,
        parent_sha256=hashlib.sha256(PARENT.read_bytes()).hexdigest(),
        proof='PROOF.md',
        proof_boundary='New positive-zero existence equivalence, using pinned Carrier65/native/K215 calibration; no fresh end-to-end proof assistant compilation.')
    return out

def lift_integer(p):
    rows=[];variables=[]
    for name in p['witnesses']:
        aa,bb,cc=name+'_a',name+'_b',name+'_c'
        variables.extend([aa,bb,cc])
        rows.extend([
            [name+'_a2','*',aa,aa],[name+'_b2','*',bb,bb],
            [name+'_c1','+',cc,1],[name+'_tri','*',cc,name+'_c1'],
            [name+'_sum2','+',name+'_a2',name+'_b2'],
            [name+'_sum3','+',name+'_sum2',name+'_tri'],
            [name,'+',name+'_sum3',1]])
    rows+=p['source']
    out=dict(p);out.update(name=p['name']+'_integer39',witnesses=variables,
        witness_domain='unrestricted integers',source=rows,
        exact_degree=2*p['exact_degree'],operations=len(rows),
        operation_counts=dict(sorted(Counter(r[1] for r in rows).items())))
    return out

def main():
    for mode in ['square','oriented']:
        p=build(mode)
        (HERE/('positive13_'+mode+'.json')).write_text(json.dumps(p,indent=2,sort_keys=True)+'\n')
        z=lift_integer(p)
        (HERE/('integer39_'+mode+'.json')).write_text(json.dumps(z,indent=2,sort_keys=True)+'\n')
        print(mode,len(p['witnesses']),p['operations'],p['exact_degree'],z['operations'])

if __name__=='__main__':main()
