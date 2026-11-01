#!/usr/bin/env python3
"""Eliminate the f-square input by its defining product."""
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parent
raw=(D.parent/'adaptive-square-sums30-degree8/candidate.json').read_bytes()
if hashlib.sha256(raw).hexdigest()!='f6c88de69011dc070c3cb642cf12bc27bb20c6ee92eaabb56dc1ccd884f685ad':raise ValueError('parent pin')
p=json.loads(raw);w=p['witnesses'];assert len(w)==30 and w[18]=='fSquareVariable';w=w[:18]+w[19:]
table={r[0]:r for r in p['source']}
expected={'f2':['f2','*','f','f'],'fSquareDifference':['fSquareDifference','-','fSquareVariable','f2'],'fSquareConstraint':['fSquareConstraint','*','fSquareDifference','fSquareDifference'],'addFSquare':['addFSquare','+','addEll','fSquareConstraint']}
if any(table.get(k)!=v for k,v in expected.items()):raise ValueError('parent binding differs')
rows=[]
for name,op,left,right in p['source']:
 if name in ('fSquareDifference','fSquareConstraint','addFSquare'):continue
 left={'fSquareVariable':'f2','addFSquare':'addEll'}.get(left,left)
 right={'fSquareVariable':'f2','addFSquare':'addEll'}.get(right,right)
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
if len(w)!=29 or len(rows)!=135:raise ValueError(('unexpected size',len(w),len(rows)))
out={'scope':'Candidate only; model and native no-zero equivalence remain open.','witnesses':w,'fixed_numerals':p['fixed_numerals'],'source':rows,'output':p['output'],'operations':len(rows)}
(D/'candidate.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: 29 variables, 135 live circuit rows; model and native equivalences remain open')
