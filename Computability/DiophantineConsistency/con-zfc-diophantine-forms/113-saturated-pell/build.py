#!/usr/bin/env python3
"""Rebuild the four saturated equations and four intermediate candidates."""
from pathlib import Path
from collections import Counter
import json

ROOT=Path(__file__).resolve().parent
SRC=ROOT/'source/parents'
HERE=ROOT/'equations'

def build(parent_path, name, both=False, transport_only=False):
    parent=json.loads(parent_path.read_text())
    direct='x' in parent['witnesses']
    bt='B' if direct else 'Bt'
    rows=[]
    for row in parent['source']:
        n,op,a,b=row
        if n in {'qm1L','W','WBt'}: continue
        if not transport_only and n=='HI': continue
        if not transport_only and n in {'Dp','I2'}: continue
        if not transport_only and n=='I':
            rows.append(row)
            rows.append(['Cf','*','Ap1','I'])
            rows.append(['Saux','*','Am1','Cf'])
            continue
        if not transport_only and n=='DpI2': row=[n,'*','Saux','I']
        if not transport_only and n=='Q': row=[n,'*','Saux','Saux']
        if not transport_only and n=='L':
            rows.append(['L','*','k','Tp'])
            if both: rows.append(['threeCt','*',3,'V0kk'])
            continue
        if n=='nV':
            rows.append(row)
            if not transport_only:
                rows.append(['nVCf','+','nV','Cf'])
                if both: rows.append(['nVCfCt','+','nVCf','threeCt'])
            rows.append(['LBt','*','L',bt])
            rows.append(['center','-','nV' if transport_only else 'nVCfCt' if both else 'nVCf','LBt'])
            continue
        if n=='Hn': row=[n,op,a,'center']
        if n=='q3WBt': row=['q3Bt','*','q3',bt]
        if n==('inner0' if direct else 'inner'): row=[n,op,a,'q3Bt']
        rows.append(row)
    known=set(parent['witnesses']+parent['fixed_numerals']); deps={}; deg={x:1 for x in parent['witnesses']}|{x:0 for x in parent['fixed_numerals']}
    for n,op,a,b in rows:
        if n in known or any(isinstance(v,str) and v not in known for v in (a,b)): raise ValueError(('topology',n,a,b))
        known.add(n);deps[n]=(a,b)
        da,db=(deg[v] if isinstance(v,str) else 0 for v in (a,b))
        deg[n]=da+db if op=='*' else max(da,db)
    live=set();todo=[parent['output']]
    while todo:
        v=todo.pop()
        if not isinstance(v,str) or v in live:continue
        live.add(v);todo.extend(deps.get(v,()))
    if live!=known:raise ValueError(('dead',known-live))
    obj={k:parent[k] for k in ['domain','witnesses','fixed_numerals','output','coefficient_binding']}
    obj.update(name=name,source=rows,operations=len(rows),operation_breakdown=dict(Counter(r[1] for r in rows)),syntactic_degree=deg['N'],parent=str(parent_path.relative_to(ROOT)),centering='transport_only' if transport_only else 'both' if both else 'strong_only')
    page=json.loads((SRC/'one-page-short10.json').read_text())
    obj['coefficient_binding']=page['coefficient_binding']
    obj['coefficient_binding']['path']='coefficients/compact44_bfs/'
    obj['exact_degree']={'strong_center':358,'both_centers':354,'direct_strong_center':330,'direct_both_centers':327}[name]
    obj['proof']='source/proofs/independent_three_root_centering.md and report_parts/centered_degree_proof.tex; inherited ordinary calibration identified in source/README.md'
    return obj

def all_equations():
    result={}
    for direct in [False,True]:
        parent=SRC/(('ten-positive-direct-zero-offset' if direct else 'ten-positive-zero-offset')+'.json')
        prefix='direct_' if direct else ''
        result[prefix+'strong_center']=build(parent,prefix+'strong_center')
        result[prefix+'both_centers']=build(parent,prefix+'both_centers',both=True)
    from build_saturation import saturate
    for direct in [False,True]:
        base=result[('direct_' if direct else '')+'strong_center']
        for sharp in [False,True]:
            obj=saturate(base,sharp);result[obj['name']]=obj
    return result

if __name__=='__main__':
    import sys
    check='--check' in sys.argv
    for name,obj in all_equations().items():
        path=HERE/(name+'.json'); data=json.dumps(obj,indent=2)+'\n'
        if check:
            if path.read_text()!=data: raise ValueError('rebuild mismatch: '+name)
        else:
            path.write_text(data)
        print(name,obj['operations'],obj['exact_degree'])
