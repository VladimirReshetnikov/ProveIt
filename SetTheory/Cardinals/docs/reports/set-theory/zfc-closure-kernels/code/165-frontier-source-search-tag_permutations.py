from pathlib import Path
import json,itertools
import source_language as s,source_splice as sp
P=Path(__file__).resolve().parent;root=s.tree(json.loads((P/'sites215.json').read_text()))
x=json.loads((P/'dag215.json').read_text());ns=[]
for n in x['nodes']:ns.append(tuple(n)if isinstance(n[0],str)else tuple(ns[i]for i in n))
calls=json.loads((P/'constructor_calls.json').read_text());one=ns[37];base=ns[76]
def parens(xx):
 if len(xx)==1:return xx
 return [(a,b)for i in range(1,len(xx))for a in parens(xx[:i])for b in parens(xx[i:])]
def options(old,new):
 if old==new:return[('same',)]
 if new<old:return[('del',t)for t in itertools.combinations(range(old),old-new)]
 # Append to the base or replace one old increment by a run.
 out=[('base',p)for p in parens([base]+[one]*(new-old))]
 for j in range(old):
  out += [('inc',j,p)for p in parens([one]*(new-old+1))]
 return out
ans=[]
for tags in itertools.permutations([0,2,3]):
 mp={0:tags[0],1:1,2:tags[1],3:tags[2]}
 if all(k==v for k,v in mp.items()):continue
 opts=[options(k,mp[k])for k in(0,2,3)]
 best=999;hits=[];count=0
 for choices in itertools.product(*opts):
  sty=dict(zip((0,2,3),choices));edits={}
  for c in calls:
   old=c['tag'];new=mp[old]
   if old==1 or old==new:continue
   opt=sty[old]
   if opt[0]=='del':
    for j in opt[1]:edits[c['basehi']+j,c['basehi']+j+1]=None
   elif opt[0]=='base':edits[c['lo'],c['basehi']]=opt[1]
   elif opt[0]=='inc':edits[c['basehi']+opt[1],c['basehi']+opt[1]+1]=opt[2]
   else:raise ValueError(opt)
  try:t=sp.apply_closed_splices(root,edits)
  except AssertionError:continue
  count+=1;score=len(sp.nodes(t))
  if score<best:best=score;hits=[]
  if score==best:hits.append((choices,t))
 print('BEST',mp,best,'valid',count,'hits',len(hits),flush=True)
 files=[]
 for k,(choices,t)in enumerate(hits[:8]):
  file=P/f'tags_{tags[0]}1{tags[1]}{tags[2]}_{k}_{best}.json';file.write_bytes(s.compact(s.sites(t)));m=s.metrics(t);print(file.name,m,flush=True);files.append({'file':str(file),**m})
 ans.append({'tags':mp,'best':best,'variants':count,'hits':len(hits),'files':files})
(P/'tag_permutation_summary.json').write_text(json.dumps(ans,indent=2)+'\n')

