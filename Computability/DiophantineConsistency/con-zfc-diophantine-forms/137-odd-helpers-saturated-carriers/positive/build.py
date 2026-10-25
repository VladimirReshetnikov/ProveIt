#!/usr/bin/env python3
"""Materialize the q-cube-normalized Pell-double product-square family."""
import json, hashlib, sys
from pathlib import Path
from collections import Counter
H=Path(__file__).resolve().parent
for old,count,degree in [(84,81,750),(85,82,560)]:
    parent=json.loads((H/f'source/equation_{old}.json').read_text())
    rows=[]
    for n,op,a,b in parent['source']:
        if n in {'q2','q3','P1','qm1Y','q3Bt','inner'}: continue
        rows.append([n,op,a,b])
        if n=='q':rows += [['q2','*','q','q'],['q3','*','q2','q'],['Y','*','q3','s']]
    changes={
        'P1mu2':['*','bJ','mu2'],
        'mu2inner':['*','mu2','Bt'],
        'P1e':['*','bJ','e'],
        'brk':['+','mu2inner','P1e'],
        'Znum':['-','Zpart1','Zpart2']}
    rows=[[n,*changes.get(n,[op,a,b])] for n,op,a,b in rows]
    obj={k:parent[k] for k in ['domain','fixed_numerals','coefficient_binding']}
    obj['coefficient_binding']=json.loads((H/'coefficients/BINDING.json').read_text())
    obj.update(witnesses=['J','F','alpha','i','T','w','s','n','eta','zeta'],
        name=f'qcube_pell_double_product_{parent["transport_weight"]}',
        operations=len(rows),operation_breakdown=dict(Counter(r[1] for r in rows)),
        exact_degree=degree,transport_weight=parent['transport_weight'],output='N',source=rows,
        proof='PROOF.md',proof_status='Ordinary unbounded arithmetic equivalence at the complete inherited directly indexed BFS943 tuple; no new formal endpoint or consistency proof.',
        parent_sha256=hashlib.sha256((H/f'source/equation_{old}.json').read_bytes()).hexdigest())
    if len(rows)!=count:raise ValueError((old,len(rows)))
    text=json.dumps(obj,indent=2)+'\n'; p=H/f'equation_{count}.json'
    if '--check' in sys.argv:
        if p.read_text()!=text:raise ValueError(f'Rebuild mismatch {p}')
    else:p.write_text(text)
    print(f'{p.name}: {count} operations, exact degree {degree}, split {obj["operation_breakdown"]}')
