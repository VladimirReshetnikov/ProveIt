#!/usr/bin/env python3
"""Propose a degree-30 fourteen-variable sum-of-squares graph."""
from collections import Counter
import hashlib
import json
from pathlib import Path
D=Path(__file__).resolve().parent
P=D.parent/'adaptive-square-sums/candidate.json'
raw=P.read_bytes()
if hashlib.sha256(raw).hexdigest()!='11fb3c192fb3a8ab9204ef0a5401198d986e002242e4f48442147aa356263828':
    raise ValueError('parent mismatch')
p=json.loads(raw);rows=[]
for row in p['source']:
    name,op,a,b=row
    if name=='g81':
        rows.append(['squareWitness','-','squareVariable',1])
        rows.append([name,op,a,'squareWitness'])
    else:rows.append(row)
rows += [['squareDifference','-','squareWitness','g80'],
         ['squareConstraint','*','squareDifference','squareDifference'],
         ['sumWithConstraint','+','sumSquares','squareConstraint']]
names=p['witnesses']+['squareVariable'];ports=p['fixed_numerals'];known=set(names+ports)
for name,op,a,b in rows:
    if name in known or op not in '+-*' or any(not isinstance(x,int) and x not in known for x in (a,b)):
        raise ValueError(('invalid row',name))
    known.add(name)
table={r[0]:r for r in rows};live={'sumWithConstraint'};todo=list(live)
while todo:
    name=todo.pop()
    if name in table:
        for value in table[name][2:]:
            if isinstance(value,str) and value not in live:live.add(value);todo.append(value)
if not set(table)<=live or not set(names+ports)<=live:raise ValueError('dead input or gate')
if len(rows)!=91:raise ValueError(('count',len(rows)))
data={'name':'adaptive-14-variable-square-witness-degree30','scope':'Candidate only; no zero-set transfer or iPRA proof is claimed.',
      'parent_sha256':hashlib.sha256(raw).hexdigest(),'witnesses':names,'fixed_numerals':ports,
      'source':rows,'output':'sumWithConstraint','operations':len(rows),
      'operation_breakdown':dict(sorted(Counter(r[1] for r in rows).items()))}
out=D/'candidate.json';out.write_text(json.dumps(data,indent=2)+'\n')
print('CANDIDATE',len(rows),'live operations',data['operation_breakdown'],'sha256',hashlib.sha256(out.read_bytes()).hexdigest())
