from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parent
p=D.parent/'adaptive-square-sums50/candidate.json';raw=p.read_bytes()
if hashlib.sha256(raw).hexdigest()!='3367ebedd1207d9966944795a27e9ad9d7f987b97a50bc996cbf2600739dba12':raise ValueError('parent pin')
d=json.loads(raw);w=d['witnesses'];
if w[40:42]!=['qPositive','qNegative']:raise ValueError('unexpected witness order')
w=w[:40]+['qValueVariable']+w[42:];rows=[]
for name,op,a,b in d['source']:
 if name=='Q':
  if [op,a,b]!=['-','qPositive','qNegative']:raise ValueError('unexpected Q gate')
  continue
 a='qValueVariable' if a=='Q' else a;b='qValueVariable' if b=='Q' else b
 if a in ('qPositive','qNegative') or b in ('qPositive','qNegative'):raise ValueError(('unexpected input',name))
 rows.append([name,op,a,b])
table={r[0]:r for r in rows};known=set(w+d['fixed_numerals']);live={d['output']};todo=list(live)
for name,op,a,b in rows:
 if name in known or any(not isinstance(x,int) and x not in known for x in (a,b)):raise ValueError(('bad row',name))
 known.add(name)
while todo:
 name=todo.pop()
 if name in table:
  for x in table[name][2:]:
   if isinstance(x,str) and x not in live:live.add(x);todo.append(x)
if not set(table)<=live or not set(w+d['fixed_numerals'])<=live:raise ValueError('dead node')
out={'scope':'Candidate only; combined model zero equivalence and native iPRA transfer remain open.','witnesses':w,'fixed_numerals':d['fixed_numerals'],'source':rows,'output':d['output'],'operations':len(rows)}
(D/'candidate.json').write_text(json.dumps(out,indent=2)+'\n');print(len(w),'variables;',len(rows),'operations')
