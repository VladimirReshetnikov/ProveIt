from pathlib import Path
import json,itertools
import source_language as s,source_splice as sp
P=Path('/dev/shm/zfc214_68350ec13e56/source_work');x=json.loads((P/'dag215.json').read_text());ns=[]
for n in x['nodes']:ns.append(tuple(n)if isinstance(n[0],str)else tuple(ns[i]for i in n))
root=ns[x['root']]
A=(ns[36],ns[40]);B=(ns[34],(ns[47],ns[7]))
assert sp.boundary(A)==sp.boundary(B)==(0,0,False)
def sim(n,r):
 rr=s.sites((n,('CH',None)));g=sp.cfg_intervals(rr);q=0
 for it in range(1000000):
  o,k,dest=g[q]
  if o=='CH':return r,it
  if o=='CI':r[k]+=1;q=dest[0]
  elif o=='CD':
   if r[k]:r[k]-=1;q=dest[1]
   else:q=dest[0]
  else:q=dest[0]
 raise Exception('TIMEOUT')
def parens(xx):
 if len(xx)==1:yield xx[0];return
 for i in range(1,len(xx)):
  for a in parens(xx[:i]):
   for b in parens(xx[i:]):yield(a,b)
dups=list(parens([A,B,ns[46],ns[39],ns[49]]))
for du in dups[:1]:
 for a,b in itertools.product(range(5),repeat=2):
  r=[0,a,b,17,18,19,0,0,20];out,it=sim(du,r)
  assert out==[0,a,(a+b)*(a+b+1)//2+b,17,18,19,0,0,20],(a,b,out)
best=1000;ans=[]
# binder types I,R,Q,E, then DUP and enough +1 operations to obtain E on top
for tag in range(4):
 for ix,du in enumerate(dups):
  seq=[ns[60],ns[67],ns[76]]+[ns[37]]*tag+[du]+[ns[37]]*(3-tag)
  # Keep first canonical AB plus constructor together; enumerate last-level reassociations sparsely
  for j,n in enumerate(parens([ns[68],sp.serial([ns[76]]+[ns[37]]*tag),du]+[ns[37]]*(3-tag))):
   new=sp.apply_closed_splices(root,{(643,805):n});score=len(sp.nodes(new))
   if score<best:best=score;ans=[];print('BEST',best,'tag',tag,'dup',ix,'p',j,flush=True)
   if score==best:
    file=P/f'G_dup_{tag}_{ix}_{j}_{score}.json';file.write_bytes(s.compact(s.sites(new)));ans.append({'tag':tag,'dup':ix,'paren':j,**s.metrics(new),'file':str(file)})
(P/'G_dup_summary.json').write_text(json.dumps({'best':best,'results':ans,'DUP':s.sites(dups[0]),'small_check_pairs':25},indent=2)+'\n')

