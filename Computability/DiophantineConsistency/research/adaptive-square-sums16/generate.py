#!/usr/bin/env python3
"""Candidate lower-degree equation naming the positive main scale U."""
from collections import Counter
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parent
parent=D.parent/'adaptive-square-sums15/candidate.json';raw=parent.read_bytes()
if hashlib.sha256(raw).hexdigest()!='17af36e8443655114196bc9795555b5c17756e3c9e63ff07686c71f8564795b0':raise ValueError('parent pin')
p=json.loads(raw);rows=[]
for name,op,a,b in p['source']:
    if name in ('g54','g58','g62'):
        a='mainScaleVariable' if a=='U' else a;b='mainScaleVariable' if b=='U' else b
    rows.append([name,op,a,b])
rows += [['mainScaleDifference','-','mainScaleVariable','U'],['mainScaleConstraint','*','mainScaleDifference','mainScaleDifference'],
         ['finalWithMainScale','+','finalWithScale','mainScaleConstraint']]
witnesses=p['witnesses']+['mainScaleVariable'];known=set(witnesses+p['fixed_numerals'])
for name,op,a,b in rows:
    if name in known or op not in '+-*' or any(not isinstance(x,int) and x not in known for x in (a,b)):raise ValueError(('bad row',name))
    known.add(name)
table={r[0]:r for r in rows};live={'finalWithMainScale'};todo=list(live)
while todo:
    name=todo.pop()
    if name in table:
        for x in table[name][2:]:
            if isinstance(x,str) and x not in live:live.add(x);todo.append(x)
if len(rows)!=96 or not set(table)<=live or not set(witnesses+p['fixed_numerals'])<=live:raise ValueError('liveness')
out={'name':'adaptive-16-variable-three-witness-candidate','scope':'Candidate only; zero-set equivalence and iPRA transfer are open.',
     'parent_sha256':hashlib.sha256(raw).hexdigest(),'witnesses':witnesses,'fixed_numerals':p['fixed_numerals'],
     'source':rows,'output':'finalWithMainScale','operations':len(rows),
     'operation_breakdown':dict(sorted(Counter(r[1] for r in rows).items()))}
path=D/'candidate.json';path.write_text(json.dumps(out,indent=2)+'\n')
print('CANDIDATE',len(rows),'live gates',out['operation_breakdown'],'sha',hashlib.sha256(path.read_bytes()).hexdigest())
