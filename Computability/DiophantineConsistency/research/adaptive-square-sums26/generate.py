#!/usr/bin/env python3
"""Candidate degree reduction by naming four positive polynomial values."""
from collections import Counter
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parent
parent=D.parent/'adaptive-square-sums22/candidate.json';raw=parent.read_bytes()
if hashlib.sha256(raw).hexdigest()!='c28b531267b04465725ac44248f10867cb779a8e61236772f0ceabc1a33db878':raise ValueError('parent pin')
p=json.loads(raw);rows=[]
replacements={'q3':'cubeVariable','g55':'productVariable','f2':'fSquareVariable','c2':'cSquareVariable'}
for name,op,a,b in p['source']:
    a=replacements.get(a,a);b=replacements.get(b,b)
    rows.append([name,op,a,b])
for label,var,old in [('cube','cubeVariable','q3'),('product','productVariable','g55'),('fSquare','fSquareVariable','f2'),('cSquare','cSquareVariable','c2')]:
    rows += [[label+'Difference','-',var,old],[label+'Constraint','*',label+'Difference',label+'Difference']]
for label,prior in [('Cube','finalWithNamedValues'),('Product','addCube'),('FSquare','addProduct'),('CSquare','addFSquare')]:
    rows.append(['add'+label,'+',prior,label[0].lower()+label[1:]+'Constraint'])
witnesses=p['witnesses']+['cubeVariable','productVariable','fSquareVariable','cSquareVariable'];known=set(witnesses+p['fixed_numerals'])
for name,op,a,b in rows:
    if name in known or op not in '+-*' or any(not isinstance(x,int) and x not in known for x in (a,b)):raise ValueError(('bad row',name))
    known.add(name)
table={r[0]:r for r in rows};live={'addCSquare'};todo=list(live)
while todo:
    name=todo.pop()
    if name in table:
        for x in table[name][2:]:
            if isinstance(x,str) and x not in live:live.add(x);todo.append(x)
if len(rows)!=124 or not set(table)<=live or not set(witnesses+p['fixed_numerals'])<=live:raise ValueError(('liveness',len(rows)))
out={'name':'adaptive-26-variable-four-more-names-candidate','scope':'Candidate only; zero-set equivalence and iPRA transfer are open.',
     'parent_sha256':hashlib.sha256(raw).hexdigest(),'witnesses':witnesses,'fixed_numerals':p['fixed_numerals'],
     'source':rows,'output':'addCSquare','operations':len(rows),
     'operation_breakdown':dict(sorted(Counter(r[1] for r in rows).items()))}
path=D/'candidate.json';path.write_text(json.dumps(out,indent=2)+'\n')
print('CANDIDATE',len(rows),'live gates',out['operation_breakdown'],'sha',hashlib.sha256(path.read_bytes()).hexdigest())
