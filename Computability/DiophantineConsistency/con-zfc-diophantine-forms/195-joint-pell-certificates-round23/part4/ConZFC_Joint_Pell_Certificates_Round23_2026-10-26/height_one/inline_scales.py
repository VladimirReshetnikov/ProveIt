"""Expand rare scale factors into repeated signed source-variable occurrences."""
from inline_constants import normalize as parent_normalize

def normalize(source,split=False,chain=True,mode='product_first',budget=0,pairmode='balanced',scale_budget=0,maxscale=4):
 n=parent_normalize(source,split=split,chain=chain,mode=mode,budget=budget,pairmode=pairmode);vs=n['variables'];rows=n['rows'];gone=set();records=[]
 for k,v in reversed(list(enumerate(vs))):
  if v['kind']!='scale' or v['coefficient']>maxscale:continue
  c,x=v['coefficient'],v['variable'];row=next(r for r in rows if r['kind']=='scale' and r['coefficient']==c and r['variable']==x)
  extra=sum(c**m.count(k)-1 for r in rows if r is not row for z,m in r['terms'] if k in m)-len(row['terms'])
  if extra>scale_budget:continue
  newrows=[]
  for r in rows:
   if r is row:continue
   rr=dict(r);rr['terms']=[]
   for z,m in r['terms']:
    multiplicity=c**m.count(k);mon=[x if i==k else i for i in m];rr['terms'].extend([[z,mon[:]] for _ in range(multiplicity)])
   newrows.append(rr)
  rows=newrows;gone.add(k);records.append((c,x,extra))
 # Delete constructors not reachable from any source row after inlining.
 nv=n['original_variables'];defs={max(i for z,m in r['terms'] for i in m):r for r in rows if r['kind']!='source'};sr=[r for r in rows if r['kind']=='source'];live={i for r in sr for z,m in r['terms'] for i in m if i>=nv};todo=list(live)
 while todo:
  i=todo.pop()
  for z,m in defs[i]['terms']:
   for j in m:
    if j>=nv and j not in live:live.add(j);todo.append(j)
 keep=list(range(nv))+sorted(live);ren={i:j for j,i in enumerate(keep)};n['variables']=[vs[i] for i in keep];n['rows']=[defs[i] for i in sorted(live)]+sr
 for r in n['rows']:r['terms']=[[z,[ren[i] for i in m]] for z,m in r['terms']]
 n['constant_count']=sum(v['kind']=='constant' for v in n['variables']);n['scale_count']=sum(v['kind']=='scale' for v in n['variables']);n['scale_inlining']=records
 return n
