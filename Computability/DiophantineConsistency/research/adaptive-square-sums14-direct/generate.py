#!/usr/bin/env python3
"""Candidate using a positive variable directly for the ordinate square."""
from collections import Counter
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parent
parent=D.parent/'adaptive-square-sums14/candidate.json';raw=parent.read_bytes()
if hashlib.sha256(raw).hexdigest()!='0c7451eaadba5569f2d901867c3e80deb0663e09bd51dd6972d1949eb1f669af':raise ValueError('parent pin')
p=json.loads(raw);rows=[]
for name,op,a,b in p['source']:
    if name=='squareWitness':continue
    rows.append([name,op,'squareVariable' if a=='squareWitness' else a,'squareVariable' if b=='squareWitness' else b])
known=set(p['witnesses']+p['fixed_numerals'])
for name,op,a,b in rows:
    if name in known or op not in '+-*' or any(not isinstance(x,int) and x not in known for x in (a,b)):raise ValueError(('bad row',name))
    known.add(name)
table={r[0]:r for r in rows};live={'sumWithConstraint'};todo=list(live)
while todo:
    name=todo.pop()
    if name in table:
        for x in table[name][2:]:
            if isinstance(x,str) and x not in live:live.add(x);todo.append(x)
if len(rows)!=90 or not set(table)<=live or not set(p['witnesses']+p['fixed_numerals'])<=live:raise ValueError('liveness')
out={'name':'adaptive-14-variable-direct-square-degree30','scope':'Candidate; proof of positive square witness and native endpoint still required.',
     'parent_sha256':hashlib.sha256(raw).hexdigest(),'witnesses':p['witnesses'],'fixed_numerals':p['fixed_numerals'],
     'source':rows,'output':'sumWithConstraint','operations':len(rows),
     'operation_breakdown':dict(sorted(Counter(r[1] for r in rows).items()))}
path=D/'candidate.json';path.write_text(json.dumps(out,indent=2)+'\n')
print('CANDIDATE',len(rows),'live operations',out['operation_breakdown'],'sha',hashlib.sha256(path.read_bytes()).hexdigest())
