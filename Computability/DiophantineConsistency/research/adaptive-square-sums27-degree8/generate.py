#!/usr/bin/env python3
"""Eliminate the ell product input by its defining product."""
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parent
raw=(D.parent/'adaptive-square-sums28-degree8/candidate.json').read_bytes()
if hashlib.sha256(raw).hexdigest()!='6ddad50448c27a371e27cd90f860e30ca8632c57d539f91c2f1c08f10ed1fd27':raise ValueError('parent pin')
p=json.loads(raw);w=p['witnesses'];assert len(w)==28 and w[25]=='ellProductVariable';w=w[:25]+w[26:]
table={r[0]:r for r in p['source']}
expected={'g40':['g40','*','ellVariable','g30'],'g41':['g41','+',1,'ellProductVariable'],'ellProductDifference':['ellProductDifference','-','ellProductVariable','g40'],'ellProductConstraint':['ellProductConstraint','*','ellProductDifference','ellProductDifference'],'add_ellProduct':['add_ellProduct','+','add_product2','ellProductConstraint']}
if any(table.get(k)!=v for k,v in expected.items()):raise ValueError('parent binding differs')
rows=[]
for name,op,left,right in p['source']:
 if name in ('ellProductDifference','ellProductConstraint','add_ellProduct'):continue
 left={'ellProductVariable':'g40','add_ellProduct':'add_product2'}.get(left,left)
 right={'ellProductVariable':'g40','add_ellProduct':'add_product2'}.get(right,right)
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
if len(w)!=27 or len(rows)!=129:raise ValueError(('unexpected size',len(w),len(rows)))
out={'scope':'Candidate only; model and native no-zero equivalence remain open.','witnesses':w,'fixed_numerals':p['fixed_numerals'],'source':rows,'output':p['output'],'operations':len(rows)}
(D/'candidate.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: 27 variables, 129 live circuit rows; model and native equivalences remain open')
