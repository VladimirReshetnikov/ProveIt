"""Joint grammar reparsing of every maximal associative closed-source region."""
from pathlib import Path
from collections import Counter
from functools import lru_cache
import json,sys,random,time,argparse
sys.path.insert(0,str(Path(__file__).parent));from zero5_search import Dag,s
from environment import BASE_SOURCE

class Normal:
 def __init__(self,t,freeze_prob=0.0,seed=0):
  self.nodes=[];self.idx={};self.frozen=[];self.fidx={};self.fchoices={};self.freeze_prob=freeze_prob;self.frng=random.Random(seed);self.root=self.norm(t,True);self.reachable=set()
  def visit(q):
   if q in self.reachable:return
   self.reachable.add(q);n=self.nodes[q]
   if n[0]not in('l','f'):
    for c in n[1:]:visit(c)
  visit(self.root)
  self.words={q:list(self.nodes[q][1:])for q in self.reachable if self.nodes[q][0]=='w'}
  self.atoms=self.reachable-set(self.words)
 def add(self,n):
  if n not in self.idx:self.idx[n]=len(self.nodes);self.nodes.append(n)
  return self.idx[n]
 def norm(self,t,isroot=False):
  if s.leaf(t):return self.add(('l',*t))
  if t not in self.fchoices:self.fchoices[t]=self.frng.random()<self.freeze_prob
  if not isroot and s.boundary(t)[:2]==(0,0) and self.fchoices[t]:
   if t not in self.fidx:self.fidx[t]=len(self.frozen);self.frozen.append(t)
   return self.add(('f',self.fidx[t]))
  a,b=map(self.norm,t)
  if s.boundary(t[0])[:2]==(0,0) and s.boundary(t[1])[:2]==(0,0):
   aa=self.nodes[a][1:]if self.nodes[a][0]=='w'else(a,)
   bb=self.nodes[b][1:]if self.nodes[b][0]=='w'else(b,)
   return self.add(('w',*aa,*bb))
  return self.add(('p',a,b))
 def trial(self,seed,noise=1.0,maxzero=0):
  rng=random.Random(seed);words={q:v.copy()for q,v in self.words.items()};rules={};nextid=len(self.nodes)
  frozen_stats=[]
  for t in self.frozen:
   c=t;lead=0
   while not s.leaf(c):lead+=1;c=c[0]
   frozen_stats.append((lead,s.metrics(t)['maximum_zero_run']))
  def minimum_zero():
   @lru_cache(None)
   def f(q):
    if q in rules:
     a,b=map(f,rules[q]);return 1+a[0],max(1+a[0],a[1],b[1])
    n=self.nodes[q]
    if n[0]=='l':return 0,0
    if n[0]=='f':return frozen_stats[n[1]]
    if n[0]=='p':
     a,b=map(f,n[1:]);return 1+a[0],max(1+a[0],a[1],b[1])
    v=[f(c)for c in words[q]]
    if len(v)==1:return v[0]
    return 1+v[0][0],max(max(z for l,z in v),max(1+l for l,z in v[:-1]))
   return f(self.root)[1]
  if maxzero and minimum_zero()>maxzero:return None,None
  while any(len(v)>1 for v in words.values()):
   counts=Counter(p for v in words.values()for p in zip(v,v[1:]));ranks=[]
   for p,n in counts.items():
    # A repeated equal symbol has overlapping raw counts: count disjoint uses.
    if p[0]==p[1]:
     n=0
     for v in words.values():
      i=0
      while i+1<len(v):
       if (v[i],v[i+1])==p:n+=1;i+=2
       else:i+=1
    ranks.append((n+rng.random()*noise,p))
   if not ranks:break
   ranks.sort(reverse=True)
   for _,pair in ranks:
    q=nextid;rules[q]=pair;previous=words;words={}
    for wid,v in previous.items():
     out=[];i=0
     while i<len(v):
      if i+1<len(v)and(v[i],v[i+1])==pair:out.append(q);i+=2
      else:out.append(v[i]);i+=1
     words[wid]=out
    if not maxzero or minimum_zero()<=maxzero:nextid+=1;break
    words=previous;del rules[q]
   else:return None,None
  d=Dag()
  @lru_cache(None)
  def build(q):
   if q in rules:return d.add(tuple(build(c)for c in rules[q]))
   n=self.nodes[q]
   if n[0]=='l':return d.add(n[1:])
   if n[0]=='f':return d.intern(self.frozen[n[1]])
   if n[0]=='p':return d.add(tuple(build(c)for c in n[1:]))
   assert len(words[q])==1
   return build(words[q][0])
  root=build(self.root)
  return d,root

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,default=BASE_SOURCE);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--trials',type=int,default=2000);ap.add_argument('--noise',type=float,default=1.0);ap.add_argument('--seed',type=int,default=0);ap.add_argument('--maxzero',type=int,default=0);ap.add_argument('--freeze',type=float,default=0.0);a=ap.parse_args();a.out.mkdir(parents=True,exist_ok=True)
 rows=json.loads(a.source.read_text());tree=s.tree(rows);graph=s.graph_intervals(rows);n=Normal(tree);best=(999,999);hist=Counter();start=time.monotonic();results=[]
 print('NORMAL',len(n.atoms),'atoms',len(n.words),'words',sum(map(len,n.words.values())),'symbols',flush=True)
 for k in range(a.trials):
  if a.freeze:n=Normal(tree,a.freeze,k+a.seed)
  d,root=n.trial(k+a.seed,a.noise,a.maxzero)
  if d is None:hist[999,999]+=1;continue
  nn=len(d.reach(root));zr=d.zero[root];hist[nn,zr]+=1
  score=(nn,zr)
  if score<best:
   best=score;t=d.tree(root);ss=s.sites(t)
   assert s.graph_intervals(ss)==graph and s.graph_arithmetic(ss)[0]==graph
   name=f'best_n{nn}_z{zr}_seed{k+a.seed}';(a.out/(name+'.sites.json')).write_bytes(s.compact(ss));rec={'name':name,'seed':k+a.seed,'metrics':s.metrics(t),'cfg_identical':True};(a.out/(name+'.json')).write_text(json.dumps(rec,indent=2)+'\n');results.append(rec);print('BEST',rec,'seconds',round(time.monotonic()-start,2),flush=True)
  if(k+1)%100==0:
   print('TRIAL',k+1,'best',best,'seconds',round(time.monotonic()-start,2),flush=True);(a.out/'summary.json').write_text(json.dumps({'trials':k+1,'best':best,'histogram':[[*k,v]for k,v in sorted(hist.items())],'results':results},indent=2)+'\n')
  if nn<=205 and zr<=6:break
 (a.out/'summary.json').write_text(json.dumps({'trials':k+1,'best':best,'histogram':[[*key,v]for key,v in sorted(hist.items())],'results':results},indent=2)+'\n')
if __name__=='__main__':main()
