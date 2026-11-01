import json,hashlib,collections
p='Computability/DiophantineConsistency/research/adaptive-square-sums51/candidate.json';raw=open(p,'rb').read();assert hashlib.sha256(raw).hexdigest()=='f29404f0fb2581f8fe28fb1c1537d1236696ac3580c9e9b5c1edd347b4385c72';d=json.loads(raw);w=[x for x in d['witnesses'] if x!='qNegative'];rows=[]
for n,op,a,b in d['source']:
 if n=='Q':assert [op,a,b]==['-','qPositive','qNegative'];continue
 a='qPositive' if a=='Q' else a;b='qPositive' if b=='Q' else b;rows.append([n,op,a,b])
assert len(w)==50 and len(rows)==186
names=w+d['fixed_numerals'];Z=(0,)*len(names)
def const(x):return {Z:x} if x else {}
def plus(a,b,sign=1):
 r=a.copy()
 for k,v in b.items():r[k]=r.get(k,0)+sign*v
 return {k:v for k,v in r.items() if v}
def times(a,b):
 r={}
 for k,x in a.items():
  for l,y in b.items():
   m=tuple(i+j for i,j in zip(k,l));r[m]=r.get(m,0)+x*y
 return {k:v for k,v in r.items() if v}
def initial():return {n:{Z[:i]+(1,)+Z[i+1:]:1} for i,n in enumerate(names)}
def run(rows,v):
 for n,op,a,b in rows:
  x=const(a) if isinstance(a,int) else v[a];y=const(b) if isinstance(b,int) else v[b];v[n]=plus(x,y,1 if op=='+' else -1) if op in '+-' else times(x,y)
 return v[d['output']]
v=initial();target=run(rows,v.copy());parent=initial();parent['qPositive']=plus(parent['qPositive'],const(1));parent['qNegative']=const(1);expected=run(d['source'],parent)
assert target==expected
print('PASS',len(w),'variables',len(rows),'operations','exact output polynomial identity',len(target),'monomials', 'breakdown',dict(collections.Counter(r[1] for r in rows)))

from pathlib import Path
out={'scope':'Exploratory direct-Q reduction; Lean model replay and native endpoint pending.','witnesses':w,'fixed_numerals':d['fixed_numerals'],'source':rows,'output':d['output'],'operations':len(rows),'operation_breakdown':dict(collections.Counter(r[1] for r in rows))}
Path('Computability/DiophantineConsistency/research/adaptive-directq50/candidate.json').write_text(json.dumps(out,indent=2)+'\n')
