#!/usr/bin/env python3
"""Eliminate the scaled-index product input by its defining product."""
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parent
raw=(D.parent/'adaptive-square-sums27-degree8/candidate.json').read_bytes()
if hashlib.sha256(raw).hexdigest()!='1982b2f164b9b72f965050e3a26cec751f7d0839c2da0cbe3cc020b7e6fc0170':raise ValueError('parent pin')
p=json.loads(raw);w=p['witnesses'];assert len(w)==27 and w[25]=='scaledIndexVariable';w=w[:25]+w[26:]
table={r[0]:r for r in p['source']}
expected={'I':['I','*','cSquareVariable','i'],'g71':['g71','*','scaledIndexVariable','scaledIndexVariable'],'scaledIndexDifference':['scaledIndexDifference','-','scaledIndexVariable','I'],'scaledIndexConstraint':['scaledIndexConstraint','*','scaledIndexDifference','scaledIndexDifference'],'add_scaledIndex':['add_scaledIndex','+','add_product2','scaledIndexConstraint']}
if any(table.get(k)!=v for k,v in expected.items()):raise ValueError('parent binding differs')
rows=[]
for name,op,left,right in p['source']:
 if name in ('scaledIndexDifference','scaledIndexConstraint','add_scaledIndex'):continue
 left={'scaledIndexVariable':'I','add_scaledIndex':'add_product2'}.get(left,left)
 right={'scaledIndexVariable':'I','add_scaledIndex':'add_product2'}.get(right,right)
 rows.append([name,op,left,right])
known=set(w+p['fixed_numerals']);table={r[0]:r for r in rows}
for name,op,left,right in rows:
 if name in known or op not in ('+','-','*') or any(isinstance(x,str) and x not in known for x in (left,right)):raise ValueError(('bad topological row',name))
 known.add(name)
live={p['output']};todo=list(live)
while todo:
 name=todo.pop()
 if name in table:
  for dep in table[name][2:]:
   if isinstance(dep,str) and dep not in live:live.add(dep);todo.append(dep)
if set(table)-live or set(w+p['fixed_numerals'])-live:raise ValueError('dead node or input')
if len(w)!=26 or len(rows)!=126:raise ValueError(('unexpected size',len(w),len(rows)))
out={'scope':'Candidate only; model and native no-zero equivalence remain open.','witnesses':w,'fixed_numerals':p['fixed_numerals'],'source':rows,'output':p['output'],'operations':len(rows)}
(D/'candidate.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: 26 variables, 126 live circuit rows; model and native equivalences remain open')
