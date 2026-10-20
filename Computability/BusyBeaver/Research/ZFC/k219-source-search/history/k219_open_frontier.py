import json,time,functools,collections
from pathlib import Path
exec(open('/tmp/k219_probe.py').read().split('# finite Cartesian')[0])
class Dag:
 def __init__(self):self.nodes=[];self.ids={};self.length=[];self.sig=[];self.depth=[];self.lead=[];self.zero=[]
 def add(self,n):
  if n in self.ids:return self.ids[n]
  i=len(self.nodes);self.ids[n]=i;self.nodes.append(n)
  if isinstance(n[0],str):
   op,r=n;self.length.append(1);self.depth.append(0);self.lead.append(0);self.zero.append(0)
   self.sig.append(((('N',0),),) if op=='CI' else ((('B',1),('N',0)),) if op=='CD' else (((('B' if op=='CB' else 'C'),r),),) if op in ('CB','CC') else ((),))
  else:
   a,b=n;la=self.length[a];self.length.append(la+self.length[b]);self.depth.append(1+max(self.depth[a],self.depth[b]));self.lead.append(1+self.lead[a]);self.zero.append(max(1+self.lead[a],self.zero[a],self.zero[b]))
   def tr(t,side):
    if isinstance(t,int):return t+(la if side else 0)
    k,v=t
    if side==0:
     if k=='N':return la
     if k=='B':return ('N',0) if v==1 else ('B',v-1)
     return t
    if k=='C':return 0 if v==1 else ('C',v-1)
    return t
   self.sig.append(tuple(tuple(tr(t,0) for t in ts) for ts in self.sig[a])+tuple(tuple(tr(t,1) for t in ts) for ts in self.sig[b]))
  return i
 def intern(self,t):return self.add(t if leaf(t) else (self.intern(t[0]),self.intern(t[1])))
 def reach(self,r):
  seen=set();todo=[r]
  while todo:
   i=todo.pop()
   if i in seen:continue
   seen.add(i)
   if not isinstance(self.nodes[i][0],str):todo.extend(self.nodes[i])
  return seen
 def tree(self,r):
  @functools.lru_cache(None)
  def rec(i):
   n=self.nodes[i];return n if isinstance(n[0],str) else (rec(n[0]),rec(n[1]))
  return rec(r)
started=time.monotonic();total=0;exact=0;scored=0;best=206;besthits=[];pernode=[]
for node_index in range(206):
 d=Dag();root=d.intern(tree);old_count=len(d.nodes);x=node_index
 if isinstance(d.nodes[x][0],str) or d.length[x]>400:continue
 original_sig=d.sig[x];frontiers=set()
 for method in ('large','small','left','right','depth'):
  f=[x]
  while len(f)<8:
   opts=[i for i,q in enumerate(f) if not isinstance(d.nodes[q][0],str)]
   if not opts:break
   if method=='large':i=max(opts,key=lambda i:d.length[f[i]])
   elif method=='small':i=min(opts,key=lambda i:d.length[f[i]])
   elif method=='left':i=opts[0]
   elif method=='right':i=opts[-1]
   else:i=max(opts,key=lambda i:d.depth[f[i]])
   f[i:i+1]=d.nodes[f[i]]
   if len(f)>=3:frontiers.add(tuple(f))
 parents=collections.defaultdict(set)
 for q,n in enumerate(d.nodes[:old_count]):
  if not isinstance(n[0],str):
   for c in n:parents[c].add(q)
 affected={x};todo=[x]
 for q in todo:
  for p in parents[q]:
   if p not in affected:affected.add(p);todo.append(p)
 seenroots=set();nt=ne=0
 for f in sorted(frontiers,key=lambda f:(len(f),f)):
  @functools.lru_cache(None)
  def shapes(i,j):
   if j-i==1:return (f[i],)
   return tuple(d.add((a,b)) for k in range(i+1,j) for a in shapes(i,k) for b in shapes(k,j))
  for nx in shapes(0,len(f)):
   if nx in seenroots:continue
   seenroots.add(nx);nt+=1;total+=1
   if d.sig[nx]!=original_sig:continue
   ne+=1;exact+=1
   mapping={x:nx}
   for q in sorted(affected):
    if q==x:continue
    a,b=d.nodes[q];mapping[q]=d.add((mapping.get(a,a),mapping.get(b,b)))
   nr=mapping[root]
   if d.zero[nr]>6:continue
   scored+=1;score=len(d.reach(nr))
   if score<best:
    best=score;print('BEST',best,'node',x,'leaves',d.length[x],'frontier',len(f),'total',total,flush=True)
    z=d.tree(nr);assert graph(leaves(z))==G
    hit={'score':score,'node':x,'old_leaves':d.length[x],'frontier':f,'frontier_lengths':[d.length[q] for q in f],'new_node':nx,'new_subtree':d.tree(nx),'old_subtree':d.tree(x),'sites':leaves(z)}
    besthits.append(hit);Path('/tmp/k219-open-best.json').write_text(json.dumps(hit))
  shapes.cache_clear()
 pernode.append({'node':x,'leaves':d.length[x],'frontiers':len(frontiers),'examined':nt,'same_open_cfg':ne})
 if node_index%20==0:print('progress',node_index,total,exact,best,round(time.monotonic()-started,1),flush=True)
result={'examined':total,'same_open_cfg':exact,'zero_run_accepted':scored,'best_dag':best,'seconds':time.monotonic()-started,'nodes':pernode,'hits':besthits}
Path('/tmp/k219-open-frontier-result.json').write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items() if k not in ('nodes','hits')},flush=True)
