from pathlib import Path
import source_language as s,source_splice as sp
import json,random,time,argparse
from functools import lru_cache
ap=argparse.ArgumentParser();ap.add_argument('--source',default='G_Q.json');ap.add_argument('--seconds',type=int,default=300);ap.add_argument('--seed',type=int,default=7);args=ap.parse_args()
random.seed(args.seed);P=Path(__file__).resolve().parent
base=s.tree(json.loads((P/args.source).read_text()));baseword=[r[1:]for r in s.sites(base)]
ns=[];lookup={};bnd=[];depth=[];iz=[];mz=[];sz=[]
def intern(n):
 if n in lookup:return lookup[n]
 i=len(ns);ns.append(n);lookup[n]=i
 if isinstance(n[0],str):
  o,a=n;bnd.append((1 if o=='CD'else a if o=='CB'else 0,a if o=='CC'else 0,o=='CH'));depth.append(0);iz.append(0);mz.append(0);sz.append(1)
 else:
  a,b=n;aa,bb=bnd[a],bnd[b]
  bnd.append((max(aa[0]-1,bb[0],0),max(aa[1],bb[1]-1,0),aa[2]or bb[2]));depth.append(1+max(depth[a],depth[b]));iz.append(1+iz[a]);mz.append(max(1+iz[a],mz[a],mz[b]));sz.append(sz[a]+sz[b])
 return i
def parse(n):return intern(n if s.leaf(n)else(parse(n[0]),parse(n[1])))
def expand(i):return ns[i] if isinstance(ns[i][0],str)else(expand(ns[i][0]),expand(ns[i][1]))
def closure(i,seen=None):
 if seen is None:seen=set()
 if i in seen:return seen
 seen.add(i);n=ns[i]
 if not isinstance(n[0],str):closure(n[0],seen);closure(n[1],seen)
 return seen
def rewrite(rt,old,new):
 memo={}
 def go(r):
  if r==old:return new
  if r in memo:return memo[r]
  n=ns[r];out=r if isinstance(n[0],str)else intern((go(n[0]),go(n[1])))
  memo[r]=out;return out
 return go(rt)
def closed(i):return bnd[i]==(0,0,False)
r=parse(base);best=(len(closure(r)),mz[r]);bestroot=r
start=time.time();iters=0;seen={r};neutral=[];record=[]
def save(r,label):
 tree=expand(r);rows=s.sites(tree);assert [x[1:]for x in rows]==baseword
 assert s.graph_intervals(rows)==s.graph_arithmetic(rows)[0]==s.graph_intervals(s.sites(base))
 out=P/f'closed_{Path(args.source).stem}_{label}_{len(closure(r))}_z{mz[r]}.json'
 out.write_bytes(s.compact(rows));print('SAVED',str(out),'nodes',len(closure(r)),'maxzero',mz[r],flush=True)
while time.time()-start<args.seconds:
 current=len(closure(r));moves=[]
 for at in closure(r):
  n=ns[at]
  if isinstance(n[0],str):continue
  for di in(0,1):
   ch=ns[n[di]]
   if isinstance(ch[0],str):continue
   a,b,c=(n[0],ch[0],ch[1])if di else(ch[0],ch[1],n[1])
   if not all(map(closed,(a,b,c))):continue
   repl=intern((intern((a,b)),c)) if di else intern((a,intern((b,c))))
   rr=rewrite(r,at,repl)
   if depth[rr]>63 or mz[rr]>6:continue
   count=len(closure(rr));objective=(count,mz[rr])
   if objective<best:
    best=objective;bestroot=rr;save(rr,'best'+str(iters))
   if count<=204 and rr not in seen:moves.append((rr,at,di,count))
 if not moves:
  r=parse(base);seen={r}
 else:
  minimum=min(x[3]for x in moves);opt=moves if random.random()<0.08 else[x for x in moves if x[3]==minimum];m=random.choice(opt);r=m[0];seen.add(r)
 iters+=1
 if iters%25==0:print('progress',iters,len(ns),best,round(time.time()-start,1),flush=True)
 if len(ns)>1000000:
  raw=expand(r);besttree=expand(bestroot);ns.clear();lookup.clear();bnd.clear();depth.clear();iz.clear();mz.clear();sz.clear()
  r=parse(raw);bestroot=parse(besttree);seen={r}
 if best[0]<202:break
save(bestroot,'final')
print('done',iters,best,len(ns),round(time.time()-start,1))

