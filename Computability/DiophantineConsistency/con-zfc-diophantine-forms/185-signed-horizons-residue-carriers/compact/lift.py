#!/usr/bin/env python3
"""Construct ordinary integer-domain equations from the positive P14 graph."""
import copy
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
source_path=ROOT/'equations/positive14_ops68_degree146.json'
source=json.loads(source_path.read_text())

for free in (['f','n','tau'],):
    spec=copy.deepcopy(source)
    rows=[]
    witnesses=[]
    for x in source['witnesses']:
        if x in free:
            witnesses.append(x)
            continue
        a,b,c=x+'_a',x+'_b',x+'_c'
        witnesses.extend([a,b,c])
        rows.extend([
            [x+'_a2','*',a,a],
            [x+'_b2','*',b,b],
            [x+'_cp1','+',c,1],
            [x+'_ccp1','*',c,x+'_cp1'],
            [x+'_sum2','+',x+'_a2',x+'_b2'],
            [x+'_sum3','+',x+'_sum2',x+'_ccp1'],
            [x,'+',x+'_sum3',1],
        ])
    rows.extend(source['source'])
    nvars=len(witnesses)
    degree=288
    spec.update({
        'name':f'integer{nvars}_degree{degree}',
        'witnesses':witnesses,
        'source':rows,
        'domain':'unrestricted integers',
        'witness_domain':'unrestricted integers',
        'operations':len(rows),
        'operation_counts':{op:sum(r[1]==op for r in rows) for op in ('*','+','-')},
        'exact_degree':degree,
        'lift':{
            'positive_polynomial':'positive14_ops68_degree146.json',
            'source_sha256':hashlib.sha256(source_path.read_bytes()).hexdigest(),
            'free_integer_coordinates':free,
            'other_coordinates':'1+a*a+b*b+c*(c+1)',
            'proof':'../INTEGER_DOMAIN.md',
        },
    })
    spec['parent']={'path':'../equations/positive14_ops68_degree146.json',
                    'sha256':hashlib.sha256(source_path.read_bytes()).hexdigest()}
    p=ROOT/'integer_equations'/f"{spec['name']}.json"
    p.parent.mkdir(exist_ok=True)
    p.write_text(json.dumps(spec,indent=2)+'\n')
    print(spec['name'], nvars, len(rows), degree)
