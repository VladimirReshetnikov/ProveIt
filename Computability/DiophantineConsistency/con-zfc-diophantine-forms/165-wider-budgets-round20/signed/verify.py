#!/usr/bin/env python3
"""Independent symbolic replay: no imports from builder or prior checkers."""
import copy,hashlib,json,sys
from pathlib import Path
from collections import defaultdict
R=Path(__file__).resolve().parent

def load(p):return json.loads(p.read_text())
def require(x,msg):
 if not x:raise ValueError(msg)
def collect(ts):
 d=defaultdict(int)
 for c,m in ts:
  require(type(c)is int and c!=0 and type(m)is list and all(type(v)is int and v>=0 for v in m),'malformed monomial')
  d[tuple(sorted(m))]+=c
 return {m:c for m,c in d.items() if c}
def linear(a,b,k):
 d=defaultdict(int,a)
 for m,c in b.items():d[m]+=k*c
 return {m:c for m,c in d.items() if c}
def multiply(a,b):
 d=defaultdict(int)
 for m,c in a.items():
  for n,v in b.items():d[tuple(sorted(m+n))]+=c*v
 return {m:c for m,c in d.items() if c}
def substitute(p,v,f):
 ans={}
 for m,c in p.items():
  prod={():c}
  for j in m:prod=multiply(prod,f if j==v else {(j,):1})
  ans=linear(ans,prod,1)
 return ans
def compaction(names,rows):
 used=sorted({v for p in rows for m in p for v in m});require(all(0<=v<len(names) for v in used),'index')
 remap=dict(zip(used,range(len(used))))
 return [names[i] for i in used],[{tuple(remap[v] for v in m):c for m,c in p.items()} for p in rows if p]
def semantic(family):
 original=load(R/('inherited_shared/candidate244/equation.json' if family=='shared' else 'power_majorant245/equation.json'))
 names=original['variables'];require(len(names)==(244 if family=='shared' else 245),'source dimension')
 rows=[];count=0
 for row in original['residuals']:
  p=collect(row['terms'])
  if row['label']=='domain_guard.4':
   count+=1;squares=[m for m,c in p.items() if c==-4];expected=12 if family=='shared' else 11
   require(len(squares)==expected and all(len(m)==2 and m[0]==m[1]for m in squares),'normalized squares')
   allowed=lambda n:('remainder'in n or n=='bootstrap.normalized_ceiling_error')
   require(all(allowed(names[m[0]]['name'])for m in squares),'semantic normalized coordinates')
   require(p.get(())==-1 and len(p)==expected+6,'sphere shape')
   p.pop(())
   for m in squares:p[m]+=2
  rows.append(p)
 require(count==1,'single changed sphere')
 return compaction(names,rows)
def replay(names,rows,stages):
 counts=defaultdict(int)
 for stage in stages:
  for h in stage:
   kind=h['kind'];counts[kind]+=1
   if kind=='row_add':
    i,j,k=h['i'],h['j'],h['k'];require(all(type(v)is int for v in [i,j,k]) and i!=j and 0<=i<len(rows) and 0<=j<len(rows),'row operation');old=rows[i];new=linear(old,rows[j],k);require(linear(new,rows[j],-k)==old,'inverse row');rows[i]=new
   elif kind in ['shear','shear_form']:
    if kind=='shear':
     i,v,k=h['i'],h['j'],h['k'];require(i!=v and 0<=i<len(names),'shear');f={(v,):1,(i,):k}
    else:v=h['variable'];f=collect(h['replacement'])
    require(0<=v<len(names) and f.get((v,))==1 and all(len(m)==1 and m[0]<len(names) for m in f),'unimodular shear form')
    back={m:(c if m==(v,) else -c) for m,c in f.items()};changed=[substitute(p,v,f) for p in rows];require([substitute(p,v,back) for p in changed]==rows,'inverse coordinate');rows=changed
   elif kind=='project':
    i,v=h['row'],h['variable'];f=collect(h['replacement']);require(0<=i<len(rows) and 0<=v<len(names) and all(len(m)<=2 and v not in m for m in f),'polynomial restoration');require(max(map(len,f),default=0)<2 or all(v not in m or len(m)==1 for j,p in enumerate(rows) if j!=i for m in p),'quadratic substitution nonlinear occurrence');unit=linear({(v,):1},f,-1);require(rows[i] in [unit,{m:-c for m,c in unit.items()}],'nonunit deletion')
    rows=[substitute(p,v,f) for p in rows];require(not rows[i],'deleted row nonzero')
   else:raise ValueError('unknown operation')
   require(all(len(m)<=2 for p in rows for m in p),'nonquadratic output')
  names,rows=compaction(names,rows)
 return names,rows,dict(counts)
def audit(name,cert=None,eq=None):
 cert=cert or load(R/'certificates'/f'{name}.json');names,rows=semantic(cert['family']);names,rows,counts=replay(names,rows,cert['stages']);eq=eq or load(R/name/'equation.json')
 require(names==eq['variables'] and rows==[collect(r['terms']) for r in eq['residuals']],'final residual system');require(eq['domain']=='unrestricted integers','domain')
 p={}
 for row in rows:p=linear(p,multiply(row,row),1)
 expanded=load(R/name/'expanded_polynomial.json');require(expanded['variables']==len(names) and collect(expanded['terms'])==p,'full expansion');require({v for m in p for v in m}==set(range(len(names))),'live index bounds')
 m=dict(variables=len(names),rows=len(rows),degree=max(map(len,p)),monomials=len(p),height=max(map(abs,p.values())),row_height=max(abs(c) for row in rows for c in row.values()))
 require(load(R/name/'METRICS.json')==m,'metrics');return dict(metrics=m,operation_counts=counts)
def main():
 for rel,sha in load(R/'SOURCE_PINS.json').items():require(hashlib.sha256((R/rel).read_bytes()).hexdigest()==sha,'source hash '+rel)
 from check_sources import audit_sources
 inherited=audit_sources()
 reports={name:audit(name) for name in load(R/'ENDPOINTS.json')};controls=[]
 for name in reports:
  e=load(R/name/'equation.json');e['residuals'][0]['terms'][0][0]+=1
  try:audit(name,eq=e)
  except ValueError:controls.append(name+':coefficient')
  else:raise ValueError('undetected coefficient')
  c=load(R/'certificates'/f'{name}.json');ops=[op for st in c['stages'] for op in st];projections=[h for h in ops if h['kind']=='project']
  if projections:
   projections[0]['replacement'][0][0]+=1
   try:audit(name,cert=c)
   except ValueError:controls.append(name+':restoration')
   else:raise ValueError('undetected restoration')
  c=load(R/'certificates'/f'{name}.json');h=c['stages'][0][0]
  if h['kind']=='shear':h['j']=h['i']
  elif h['kind']=='shear_form':
   next(t for t in h['replacement'] if t[1]==[h['variable']])[0]=2
  else:h['j']=h['i']
  try:audit(name,cert=c)
  except ValueError:controls.append(name+':noninvertible')
  else:raise ValueError('undetected noninvertible operation')
 fixture_names=[dict(name='v'),dict(name='y'),dict(name='z')]
 fixture_rows=[{(0,):1,(1,1):-1},{(0,1):1,(2,):-1}]
 fixture_op=dict(kind='project',row=0,variable=0,replacement=[[1,[1,1]]])
 try:replay(fixture_names,fixture_rows,[[fixture_op]])
 except ValueError:controls.append('quadratic_restoration_with_nonlinear_occurrence')
 else:raise ValueError('accepted nonlinear quadratic substitution')
 receipt=dict(status='PASS',python_optimized=not __debug__,endpoints=reports,inherited=inherited,rejected_corruptions=controls,scope='Exact finite source delta, unit polynomial restoration, invertible maps and every SOS coefficient; unbounded proof separately in PROOF.md.')
 out=json.dumps(receipt,indent=2);print(out)
 if len(sys.argv)>1:Path(sys.argv[1]).write_text(out+'\n')
if __name__=='__main__':main()
