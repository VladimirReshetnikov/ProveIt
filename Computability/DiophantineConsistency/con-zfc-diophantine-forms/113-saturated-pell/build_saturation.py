#!/usr/bin/env python3
from pathlib import Path
from collections import Counter
from copy import deepcopy
import json
HERE=Path(__file__).resolve().parent/'equations'

def saturate(base,sharp):
    rows=[]
    for row in base['source']:
        name,op,a,b=row
        if name=='M2':break
        if name=='Cf':
            rows.append(['UE','*','U','Dtau'])
            if sharp:rows.append(['Afull','+','Am1',1])
            rows.extend([['Cg','*','Afull' if sharp else 'Ap1','UE'],
                         ['Delta','*','Am1','Ap1'],['SE','*','Delta','UE']])
            continue
        if name=='Saux':continue
        if name=='DpI2':row=['DpI2','*','SE','U']
        elif name=='Q':row=['Q','*','Delta','DpI2']
        row=[{'I':'U','Cf':'Cg','nVCf':'nVCg'}.get(v,v) if isinstance(v,str) else v for v in row]
        rows.append(row)
    rows.extend([
        ['M2','*','Mtot','Mtot'],['dM2','*','delta','M2'],
        ['Dg','*','Dtau','Df'],['fg','*','dM2','Dg'],['fy','*','M2','Dnum'],
        ['Z2','*','Znum','Znum'],['fs','*','delta','Z2'],
        ['root_sum','+','fg','fy'],['root_gap','-','fs','root_sum'],
        ['gap2','*','root_gap','root_gap'],['fgfy','*','fg','fy'],
        ['fourfgfy','*',4,'fgfy'],['N','-','gap2','fourfgfy']])
    direct='x' in base['witnesses'];name=('direct_' if direct else '')+'saturated_'+('sharp' if sharp else 'upper')
    obj={k:deepcopy(base[k]) for k in ['witnesses','fixed_numerals','output','coefficient_binding','domain']}
    degree=(254 if sharp else 258) if direct else (278 if sharp else 283)
    obj.update(name=name,source=rows,operations=len(rows),operation_breakdown=dict(Counter(r[1] for r in rows)),exact_degree=degree,
               proof='report.pdf, sections on saturation semantics and exact degrees; inherited ordinary calibration identified in source/README.md')
    known=set(obj['witnesses']+obj['fixed_numerals']);deps={}
    for n,op,a,b in rows:
        if n in known or any(isinstance(v,str) and v not in known for v in [a,b]):raise ValueError(('topology',n,a,b))
        known.add(n);deps[n]=[a,b]
    live=set();todo=['N']
    while todo:
        v=todo.pop()
        if not isinstance(v,str) or v in live:continue
        live.add(v);todo.extend(deps.get(v,[]))
    if known!=live:raise ValueError(('dead',known-live))
    return obj

if __name__=='__main__':
    for direct in [False,True]:
        base=json.loads((HERE/(('direct_' if direct else '')+'strong_center.json')).read_text())
        for sharp in [False,True]:
            obj=saturate(base,sharp);(HERE/(obj['name']+'.json')).write_text(json.dumps(obj,indent=2)+'\n');print(obj['name'],obj['operations'],obj['exact_degree'],obj['operation_breakdown'])
