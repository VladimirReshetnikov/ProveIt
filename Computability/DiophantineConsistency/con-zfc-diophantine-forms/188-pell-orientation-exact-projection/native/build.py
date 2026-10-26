#!/usr/bin/env python3
"""Emit two exact native/Pell companions. Python standard library only."""
from collections import Counter
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
PIN = 'cdfea7d90176775d74c1c30afbe49fa78ade9897'

def require(ok, message):
    if not ok:
        raise ValueError(message)

def carrier(parent, ordinary=False):
    rows = parent['source']
    names = {row[0]:row for row in rows}
    if ordinary:
        remove = {'Lplusk','first_term','tau2','N0','hE','k_hE','Nk','prod2'}
        old_norm = ['Lplusk','first_term','tau2','N0']
        final = 'prod3'
        prev = 'prod1'
    else:
        remove = {'tau2','ell_plus_k','first_product','N0','hE','index_partial','Nk','product2'}
        old_norm = ['tau2','ell_plus_k','first_product','N0']
        final = 'product3'
        prev = 'product1'
    out = []
    for row in rows:
        name,op,left,right = row
        if name in remove:
            continue
        if name == final:
            left = prev
        out.append([name,op,left,right])
        if name == 'R':
            out += [['En','*','E','n'],['tau_partial','+','En','k'],['tau','-','tau_partial','R']]
            out += [names[x] for x in old_norm]
    witnesses = [('n' if x=='tau' else x) for x in parent['witnesses'] if x!='h']
    return out,witnesses

def build():
    fixed = json.loads((ROOT/'sources/one-page-block-mask2963_polynomial.json').read_text())
    scaled,witnesses = carrier(fixed)
    # Delta*f^2 was already a shared producer, but must precede Aaux.
    scaled_f2 = next(r for r in scaled if r[0]=='scaled_f2')
    scaled = [r for r in scaled if r[0]!='scaled_f2']
    reduced=[]
    for row in scaled:
        name,op,left,right=row
        if name=='aux_product':
            reduced += [scaled_f2,['Aaux','-','scaled_f2','Delta']]
            left='Aaux'
        reduced.append([name,op,left,right])
    old_ordinary=json.loads((ROOT/'sources/short_circuits_p68_d101.json').read_text())
    ordinary,owitnesses=carrier(old_ordinary,True)
    require(witnesses==owitnesses,'Input order mismatch')
    common={
        'schema':'literal_integer_arithmetic_dag_v1',
        'witness_domain':'strictly positive integers',
        'witnesses':witnesses,
        'fixed_numerals':fixed['fixed_numerals'],
        'coefficient_binding':{
            'manifest':'../coefficients.json',
            'repository':'VladimirReshetnikov/ProveIt',
            'commit':PIN,
            'tuple':'one-page-block-mask2963',
            'encoding':'minimal unsigned big-endian, gzip compressed',
        },
        'output':'polynomial',
        'proof':'../PROOF.md',
        'proof_boundary':'Ordinary mathematical proof composed with the pinned native/Pell/refutation calibration; no new end-to-end formal-kernel proof.'
    }
    outputs={}
    for name,rows,degree in [('q66_d118',reduced,118),('q67_d94',ordinary,94)]:
        graph=dict(common,name=name,source=rows,operations=len(rows),
                   operation_counts=dict(Counter(r[1] for r in rows)),exact_degree=degree)
        outputs[name+'.json']=graph
    return outputs

if __name__=='__main__':
    (ROOT/'circuits').mkdir(exist_ok=True)
    for name,graph in build().items():
        (ROOT/'circuits'/name).write_text(json.dumps(graph,indent=2,sort_keys=True)+'\n')
        print(name,len(graph['witnesses']),graph['operations'],graph['exact_degree'])
