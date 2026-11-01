#!/usr/bin/env python3
"""Eliminate the named W coordinate by its defining expression; candidate only."""
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parent
raw=(D.parent/'adaptive-square-sums31-degree6/candidate.json').read_bytes()
if hashlib.sha256(raw).hexdigest()!='a90ab59a3ab1b3e9b04c2b962ea79c666a3c2dc90e6941c73f5180ab73c5ee67':raise ValueError('parent pin')
p=json.loads(raw);w=p['witnesses'];assert w[18]=='wValueVariable';w=w[:18]+w[19:]
table={r[0]:r for r in p['source']}
expected={'Bt':['Bt','-','g27','g28'],'wDifference':['wDifference','-','wValueVariable','Bt'],'wConstraint':['wConstraint','*','wDifference','wDifference'],'finalWithNamedValues':['finalWithNamedValues','+','addEll','wConstraint']}
if any(table.get(k)!=v for k,v in expected.items()):raise ValueError('parent binding differs')
rows=[]
for name,op,left,right in p['source']:
 if name in ('wDifference','wConstraint','finalWithNamedValues'):continue
 left={'wValueVariable':'Bt','finalWithNamedValues':'addEll'}.get(left,left)
 right={'wValueVariable':'Bt','finalWithNamedValues':'addEll'}.get(right,right)
 rows.append([name,op,left,right])
known=set(w+p['fixed_numerals']);table={r[0]:r for r in rows}
for name,op,left,right in rows:
 if name in known or any(isinstance(x,str) and x not in known for x in (left,right)):raise ValueError(('bad topological row',name))
 known.add(name)
live={p['output']};todo=list(live)
while todo:
 name=todo.pop()
 if name in table:
  for dep in table[name][2:]:
   if isinstance(dep,str) and dep not in live:live.add(dep);todo.append(dep)
if set(table)-live or set(w+p['fixed_numerals'])-live:raise ValueError('dead node or input')
if len(w)!=30 or len(rows)!=138:raise ValueError(('unexpected size',len(w),len(rows)))
out={'scope':'Candidate only; W positivity, V orientation and native iPRA transfer remain open.','witnesses':w,'fixed_numerals':p['fixed_numerals'],'source':rows,'output':p['output'],'operations':len(rows)}
(D/'candidate.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: 30 variables, 138 live circuit rows; model and native equivalences remain open')
