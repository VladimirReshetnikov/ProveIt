from collections import Counter
from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parent
p=D.parent/'adaptive-square-sums33/candidate.json';raw=p.read_bytes()
if hashlib.sha256(raw).hexdigest()!='a7934aac8f72dc632ebc86f15fa4300106b6af2e6ab5cd73e94f8bdd4c11e735':raise ValueError('parent pin')
d=json.loads(raw);rows=[]
repl={'q2':'qSquareVariable','E':'productVariable2','g39':'psiSquareVariable','g40':'ellProductVariable','g62':'varphiSquareVariable','I':'scaledIndexVariable','y2':'ySquareVariable'}
for name,op,a,b in d['source']:
    a=repl.get(a,a);b=repl.get(b,b)
    if name=='Q':
        rows.append(['QComputed',op,a,b]);rows.append(['Q','-','qPositive','qNegative'])
    else: rows.append([name,op,a,b])
for label,var,old in [('qSquare','qSquareVariable','q2'),('product2','productVariable2','E'),('psiSquare','psiSquareVariable','g39'),('ellProduct','ellProductVariable','g40'),('varphiSquare','varphiSquareVariable','g62'),('scaledIndex','scaledIndexVariable','I'),('ySquare','ySquareVariable','y2'),('qSigned','Q','QComputed')]:
    rows += [[label+'Difference','-',var,old],[label+'Constraint','*',label+'Difference',label+'Difference']]
prev=d['output']
for label in ['qSquare','product2','psiSquare','ellProduct','varphiSquare','scaledIndex','ySquare','qSigned']:
    name='add_'+label;rows.append([name,'+',prev,label+'Constraint']);prev=name
w=d['witnesses']+list(repl.values())+['qPositive','qNegative'];known=set(w+d['fixed_numerals'])
for name,op,a,b in rows:
    if name in known or op not in '+-*' or any(not isinstance(x,int) and x not in known for x in (a,b)):raise ValueError(('bad',name))
    known.add(name)
table={r[0]:r for r in rows};live={prev};todo=[prev]
while todo:
 name=todo.pop()
 if name in table:
  for x in table[name][2:]:
   if isinstance(x,str) and x not in live:live.add(x);todo.append(x)
if not set(table)<=live or not set(w+d['fixed_numerals'])<=live:raise ValueError(('dead',set(table)-live))
out={'scope':'Candidate only; model zero equivalence and native iPRA transfer remain open.','witnesses':w,'fixed_numerals':d['fixed_numerals'],'source':rows,'output':prev,'operations':len(rows),'operation_breakdown':dict(Counter(r[1] for r in rows))}
(D/'candidate.json').write_text(json.dumps(out,indent=2)+'\n');print(len(w),len(rows),out['operation_breakdown'])
