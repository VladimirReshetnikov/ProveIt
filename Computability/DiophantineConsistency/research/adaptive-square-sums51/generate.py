from pathlib import Path
from collections import Counter
import hashlib,json
D=Path(__file__).resolve().parent
p=D.parent/'adaptive-square-sums42/candidate.json';raw=p.read_bytes()
if hashlib.sha256(raw).hexdigest()!='be55ec0103d0114973b44dfdf1dff5b5fe3a9fd24cf88dd6bf8badcaf180cac0':raise ValueError('parent pin')
d=json.loads(raw); rows=[]
repl={'g63':'deltaProductVariable','kY':'ySumVariable','b0':'offsetVariable','g54':'gammaProductVariable','g74':'timeProductVariable'}
signed={'G':('rankSeedPositive','rankSeedNegative'),'root_skew':('rootSkewPositive','rootSkewNegative')}
for name,op,a,b in d['source']:
 a=repl.get(a,a);b=repl.get(b,b)
 if name in signed:
  pos,neg=signed[name];rows.append([name+'Computed',op,a,b]);rows.append([name,'-',pos,neg])
 else:rows.append([name,op,a,b])
items=[('deltaProduct','deltaProductVariable','g63'),('rankSeed','G','GComputed'),('ySum','ySumVariable','kY'),('rootSkew','root_skew','root_skewComputed'),('offset','offsetVariable','b0'),('gammaProduct','gammaProductVariable','g54'),('timeProduct','timeProductVariable','g74')]
for label,var,old in items:rows += [[label+'Difference','-',var,old],[label+'Constraint','*',label+'Difference',label+'Difference']]
prev=d['output']
for label,_,_ in items:
 name='add_'+label;rows.append([name,'+',prev,label+'Constraint']);prev=name
w=d['witnesses']+list(repl.values())+['rankSeedPositive','rankSeedNegative','rootSkewPositive','rootSkewNegative'];known=set(w+d['fixed_numerals'])
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
