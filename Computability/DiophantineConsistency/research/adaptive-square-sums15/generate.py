#!/usr/bin/env python3
"""Propose a lower-degree 15-variable equation by naming the positive scale M."""
from collections import Counter
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parent
parent=D.parent/'adaptive-square-sums14-direct/candidate.json';raw=parent.read_bytes()
if hashlib.sha256(raw).hexdigest()!='bef34f7d0541766eea3c9a7a2abb90633e97e6df73c7b69011f195ced0f2d5b4':raise ValueError('parent pin')
p=json.loads(raw);rows=[]
for name,op,a,b in p['source']:
    if name in ('root_scaled','g39'):
        a='scaleVariable' if a=='M' else a;b='scaleVariable' if b=='M' else b
    rows.append([name,op,a,b])
rows += [['scaleDifference','-','scaleVariable','M'],['scaleConstraint','*','scaleDifference','scaleDifference'],
         ['finalWithScale','+','sumWithConstraint','scaleConstraint']]
witnesses=p['witnesses']+['scaleVariable'];known=set(witnesses+p['fixed_numerals'])
for name,op,a,b in rows:
    if name in known or op not in '+-*' or any(not isinstance(x,int) and x not in known for x in (a,b)):raise ValueError(('bad row',name))
    known.add(name)
table={r[0]:r for r in rows};live={'finalWithScale'};todo=list(live)
while todo:
    name=todo.pop()
    if name in table:
        for x in table[name][2:]:
            if isinstance(x,str) and x not in live:live.add(x);todo.append(x)
if len(rows)!=93 or not set(table)<=live or not set(witnesses+p['fixed_numerals'])<=live:raise ValueError('liveness')
out={'name':'adaptive-15-variable-two-witness-candidate','scope':'Candidate only; zero-set equivalence and iPRA transfer are open.',
     'parent_sha256':hashlib.sha256(raw).hexdigest(),'witnesses':witnesses,'fixed_numerals':p['fixed_numerals'],
     'source':rows,'output':'finalWithScale','operations':len(rows),
     'operation_breakdown':dict(sorted(Counter(r[1] for r in rows).items()))}
path=D/'candidate.json';path.write_text(json.dumps(out,indent=2)+'\n')
print('CANDIDATE',len(rows),'live gates',out['operation_breakdown'],'sha',hashlib.sha256(path.read_bytes()).hexdigest())
