#!/usr/bin/env python3
from additive_binder import *
from itertools import permutations
@cache
def assocs(xs):
 if len(xs)==1:return(xs[0],)
 return tuple((l,r)for i in range(1,len(xs))for l in assocs(xs[:i])for r in assocs(xs[i:]))
OUT=ROOT/'research_calculus/generated/constructors';OUT.mkdir(parents=True,exist_ok=True)
results=[]
for order in ['ab','ba']:
 first,second=(A,B)if order=='ab'else(B,A)
 for tag in range(4):
  ct=q(90)
  if tag==1:ct=(ct,INC)
  if tag==2:ct=(ct,(INC,INC))
  if tag==3:ct=(ct,((INC,INC),INC))
  for k,n in enumerate(assocs((first,second,ct))):
   new=s.replace(TREE,PATH,n);nm=f'{order}_{tag}_{k}';r={'name':nm,'metrics':s.metrics(new)}
   try:
    tt,m=compile_tree(T,TREE,new);r['compile']=m
    d=OUT/nm;d.mkdir(exist_ok=True);(d/'sites.json').write_bytes(s.compact(s.sites(new)));(d/'candidate.tm').write_bytes(b.table_bytes(tt))
   except Exception as e:r['error']=repr(e)
   results.append(r);print(json.dumps(r),flush=True)
(OUT/'summary.json').write_text(json.dumps(results,indent=2)+'\n')
