"""Inline selected additive constant identities, preserving every monic pivot."""
from copy import deepcopy
from collections import Counter
from fused_normalize import normalize as fused

def normalize(source,split=False,chain=True,mode='product_first',budget=0,pairmode='balanced',minconstant=5):
 n=fused(source,split=split,chain=chain,mode=mode);vs=n['variables'];gone=set();cs={v['value']:i for i,v in enumerate(vs) if v['kind']=='constant'};rows=n['rows'];records=[]
 for c,k in sorted(cs.items(),reverse=True):
  if c<minconstant:continue
  row=next(r for r in rows if r['kind']=='constant' and r['value']==c)
  uses=sum(m.count(k) for r in rows if r is not row for z,m in r['terms'])
  # Replacing one factor by a two-term affine sum adds one term per use
  # unless the factor is squared. The actual expansion is checked below.
  if uses-len(row['terms'])>budget:continue
  choices=[(a,c-a) for a in {1}|set(cs) if a<=c-a and c-a in ({1}|set(cs)) and a<c and c-a<c]
  if not choices:continue
  if pairmode=='balanced':a,b=min(choices,key=lambda ab:(ab[1],ab[0]))
  elif pairmode=='small':a,b=min(choices)
  elif pairmode=='usage':
   counts=Counter(i for r in rows for z,m in r['terms'] for i in m)
   a,b=min(choices,key=lambda ab:(-sum(counts.get(cs.get(x),0) for x in ab),ab))
  replacements=[[] if x==1 else [cs[x]] for x in (a,b)]
  newrows=[]
  for r in rows:
   if r is row:continue
   ts=[]
   for z,m in r['terms']:
    out=[[]]
    for i in m:out=[p+q for p in out for q in (replacements if i==k else [[i]])]
    ts.extend([[z,p] for p in out])
   rr=dict(r);rr['terms']=ts;newrows.append(rr)
  rows=newrows;gone.add(k);records.append((c,a,b,uses));del cs[c]
 keep=[i for i in range(len(vs)) if i not in gone];ren={i:j for j,i in enumerate(keep)}
 n['variables']=[vs[i] for i in keep];n['rows']=rows
 for r in rows:r['terms']=[[z,[ren[i] for i in m]] for z,m in r['terms']]
 n['constant_count']=sum(v['kind']=='constant' for v in n['variables']);n['constant_inlining']=records
 return n
