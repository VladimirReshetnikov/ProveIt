#!/usr/bin/env python3
"""Eliminate the main-scale square input by its defining product."""
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parent
raw=(D.parent/'adaptive-square-sums29-degree8/candidate.json').read_bytes()
if hashlib.sha256(raw).hexdigest()!='894ff6fa3205629c03de826d8984f4959c2be317bf61c46d0f393f770d113a20':raise ValueError('parent pin')
p=json.loads(raw);w=p['witnesses'];assert len(w)==29 and w[26]=='varphiSquareVariable';w=w[:26]+w[27:]
table={r[0]:r for r in p['source']}
expected={'g62':['g62','*','mainScaleVariable','mainScaleVariable'],'g65':['g65','*','varphiSquareVariable','g64'],'varphiSquareDifference':['varphiSquareDifference','-','varphiSquareVariable','g62'],'varphiSquareConstraint':['varphiSquareConstraint','*','varphiSquareDifference','varphiSquareDifference'],'add_varphiSquare':['add_varphiSquare','+','add_ellProduct','varphiSquareConstraint']}
if any(table.get(k)!=v for k,v in expected.items()):raise ValueError('parent binding differs')
rows=[]
for name,op,left,right in p['source']:
 if name in ('varphiSquareDifference','varphiSquareConstraint','add_varphiSquare'):continue
 left={'varphiSquareVariable':'g62','add_varphiSquare':'add_ellProduct'}.get(left,left)
 right={'varphiSquareVariable':'g62','add_varphiSquare':'add_ellProduct'}.get(right,right)
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
if len(w)!=28 or len(rows)!=132:raise ValueError(('unexpected size',len(w),len(rows)))
out={'scope':'Candidate only; model and native no-zero equivalence remain open.','witnesses':w,'fixed_numerals':p['fixed_numerals'],'source':rows,'output':p['output'],'operations':len(rows)}
(D/'candidate.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: 28 variables, 132 live circuit rows; model and native equivalences remain open')
