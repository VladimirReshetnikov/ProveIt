#!/usr/bin/env python3
"""Candidate degree reduction by naming three positive values and one signed pair."""
from collections import Counter
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parent
parent=D.parent/'adaptive-square-sums17/candidate.json';raw=parent.read_bytes()
if hashlib.sha256(raw).hexdigest()!='86c765e46d61a85bfa0e84a546136bcb62a9151147d355abde431579d1bd0ffc':raise ValueError('parent pin')
p=json.loads(raw);rows=[]
replacements={'c':'cVariable','a':'aVariable','ell':'ellVariable','Bt':'namedBt'}
for name,op,a,b in p['source']:
    if name=='root_skew':rows.append(['namedBt','-','wPositive','wNegative'])
    if name not in ('c','a','ell','Bt'):
        a=replacements.get(a,a);b=replacements.get(b,b)
    rows.append([name,op,a,b])
for label,var,old in [('c','cVariable','c'),('a','aVariable','a'),('ell','ellVariable','ell'),('w','namedBt','Bt')]:
    rows += [[label+'Difference','-',var,old],[label+'Constraint','*',label+'Difference',label+'Difference']]
rows += [['addC','+','finalWithRank','cConstraint'],['addA','+','addC','aConstraint'],
         ['addEll','+','addA','ellConstraint'],['finalWithNamedValues','+','addEll','wConstraint']]
witnesses=p['witnesses']+['cVariable','aVariable','ellVariable','wPositive','wNegative'];known=set(witnesses+p['fixed_numerals'])
for name,op,a,b in rows:
    if name in known or op not in '+-*' or any(not isinstance(x,int) and x not in known for x in (a,b)):raise ValueError(('bad row',name))
    known.add(name)
table={r[0]:r for r in rows};live={'finalWithNamedValues'};todo=list(live)
while todo:
    name=todo.pop()
    if name in table:
        for x in table[name][2:]:
            if isinstance(x,str) and x not in live:live.add(x);todo.append(x)
if len(rows)!=112 or not set(table)<=live or not set(witnesses+p['fixed_numerals'])<=live:raise ValueError('liveness')
out={'name':'adaptive-22-variable-four-named-values-candidate','scope':'Candidate only; zero-set equivalence and iPRA transfer are open.',
     'parent_sha256':hashlib.sha256(raw).hexdigest(),'witnesses':witnesses,'fixed_numerals':p['fixed_numerals'],
     'source':rows,'output':'finalWithNamedValues','operations':len(rows),
     'operation_breakdown':dict(sorted(Counter(r[1] for r in rows).items()))}
path=D/'candidate.json';path.write_text(json.dumps(out,indent=2)+'\n')
print('CANDIDATE',len(rows),'live gates',out['operation_breakdown'],'sha',hashlib.sha256(path.read_bytes()).hexdigest())
