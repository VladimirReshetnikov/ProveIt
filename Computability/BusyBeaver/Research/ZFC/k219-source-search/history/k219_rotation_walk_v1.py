import json,functools,random,time,collections
from pathlib import Path
exec(open('/tmp/k219_probe.py').read().split('# finite Cartesian')[0])
class Dag:
 def __init__(self):self.ns=[];self.ids={};self.br=[];self.co=[];self.lead=[];self.zero=[]
 def add(self,n):
  if n in self.ids:return self.ids[n]
  q=len(self.ns);self.ns.append(n);self.ids[n]=q
  if isinstance(n[0],str):
   op,a=n;self.br.append(1 if op=='CD' else a if op=='CB' else 0);self.co.append(a if op=='CC' else 0);self.lead.append(0);self.zero.append(0)
  else:
   a,b=n;self.br.append(max(self.br[a]-1,self.br[b],0));self.co.append(max(self.co[a],self.co[b]-1,0));self.lead.append(1+self.lead[a]);self.zero.append(max(1+self.lead[a],self.zero[a],self.zero[b]))
  return q
 def intern(self,t):return self.add(t if leaf(t) else (self.intern(t[0]),self.intern(t[1])))
 def reach(self,r):
  seen=set();todo=[r]
  while todo:
   q=todo.pop()
   if q in seen:continue
   seen.add(q)
   if not isinstance(self.ns[q][0],str):todo.extend(self.ns[q])
  return seen
 def replace(self,r,x,y):
  @functools.lru_cache(None)
  def rec(q):
   if q==x:return y
   n=self.ns[q]
   return q if isinstance(n[0],str) else self.add((rec(n[0]),rec(n[1])))
  return rec(r)
 def tree(self,r):
  @functools.lru_cache(None)
  def rec(q):
   n=self.ns[q];return n if isinstance(n[0],str) else (rec(n[0]),rec(n[1]))
  return rec(r)
d=Dag();root=d.intern(tree);rng=random.Random(219206);seen={root};frontier=[root];parents={};best=206;trials=0;accepted=0;started=time.monotonic();levels=[];hits=[]
for depth in range(1,31):
 candidates=[]
 for rr in frontier:
  for q in sorted(d.reach(rr)):
   n=d.ns[q]
   if isinstance(n[0],str):continue
   a,b=n;opts=[]
   if not isinstance(d.ns[a][0],str):
    aa,ab=d.ns[a]
    if d.br[aa]==0 and d.co[b]==0:opts.append(('R',d.add((aa,d.add((ab,b))))))
   if not isinstance(d.ns[b][0],str):
    ba,bb=d.ns[b]
    if d.br[a]==0 and d.co[bb]==0:opts.append(('L',d.add((d.add((a,ba)),bb))))
   for kind,nq in opts:
    trials+=1;nr=d.replace(rr,q,nq)
    if nr in seen:continue
    seen.add(nr)
    if d.zero[nr]>6:continue
    score=len(d.reach(nr))
    if score>207:continue
    accepted+=1;parents[nr]=(rr,q,nq,kind);candidates.append((score,rng.random(),nr))
    if score<best:
     best=score;t=d.tree(nr);assert graph(leaves(t))==G
     chain=[];cur=nr
     while cur!=root:
      pr,oq,mq,di=parents[cur];chain.append({'direction':di,'old':d.tree(oq),'new':d.tree(mq)});cur=pr
     chain.reverse();h={'score':score,'depth':depth,'sites':leaves(t),'chain':chain,'trials':trials};hits.append(h)
     Path('/tmp/k219-rotation-best.json').write_text(json.dumps(h));print('BEST',score,'depth',depth,'trials',trials,flush=True)
 if not candidates:break
 candidates.sort();frontier=[r for _,_,r in candidates[:30]]
 levels.append({'depth':depth,'candidates':len(candidates),'best':candidates[0][0],'trials':trials,'interned':len(d.ns),'elapsed':time.monotonic()-started})
 print(levels[-1],flush=True)
 if time.monotonic()-started>120:break
res={'scope':'seeded beam30 through DAG<=207/maxzero6, both open-safe global rotations; not exhaustive','best':best,'trials':trials,'accepted':accepted,'unique_roots':len(seen),'levels':levels,'hits':hits,'seconds':time.monotonic()-started}
Path('/tmp/k219-rotation-walk-result.json').write_text(json.dumps(res,indent=2)+'\n')
