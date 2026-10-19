"""Constrained dictionary repair with minimum new tree-node cost on each word.
Every physical atom retains its entry orientation. Existing good rules are
available at zero additional cost; this is a local repair, not global SLP
optimality. The emitted complete grammar is independently re-evaluated.
"""
import json,sys
import numpy as np
from pathlib import Path
from functools import lru_cache
source=Path(sys.argv[1]);d=json.loads(source.read_text());B=Path(__file__).resolve().parent/'reference_data';s=json.loads((B/'reference/grammar/closed-sequence-grammar-next22.json').read_text());sym=json.loads((B/'reference/grammar/semantic-symbols.json').read_text());enc=json.load(open(Path(__file__).resolve().parent/'inputs/canonical-map.json'))['physical_atoms'];canon=lambda w:''.join(enc[c]for c in w)
ls=(B/'reference/grammar/semantic.txt').read_text().splitlines();n,nr,na=map(int,ls[0].split());old={canon(w):(canon(w[:int(k)]),canon(w[int(k):]))for k,w,q in map(str.split,ls[1:n+1])};names={int(q):canon(w)for k,w,q in map(str.split,ls[1:n+1])};mask={enc[c]:int(m)for c,m in map(str.split,ls[n+1+nr:])};term={enc[c]:s['atoms'][k]['ast']for c,k in sym.items()};byast={int(v):names[int(q)]for q,v in s['sequence_ast_roots'].items()};g={w:(a,b)for w,a,b in d['rules']}
def evaluate(g):
 def join(a,b):return a[0]+1,max(a[0]+1,a[1],b[1]),1+max(a[2],b[2])
 @lru_cache(None)
 def wp(w):return ep(term[w])if w in term else join(*(wp(x)for x in g.get(w,old.get(w))))
 @lru_cache(None)
 def ep(i):
  if i in byast:return wp(byast[i])
  r=s['ast_dag'][i];return (0,0,0)if r[0]=='L'else join(ep(r[1]),ep(r[2]))
 return wp,ep(s['original_ast'])
def repair(w,g):
 wp,full=evaluate(g);available={x:wp(x)[0]for x in set(g)|set(term)if wp(x)[1]<=5}
 n=len(w);N=n+1;INF=10000
 left=np.full((6,N,N),INF,dtype=np.int32);right=left.copy();cut=np.full((6,N,N),-1,dtype=np.int16);strings={}
 for size in range(1,n+1):
  for a in range(n-size+1):
   b=a+size;v=w[a:b];strings[a,b]=v
   if v in available:
    h=available[v]
    if v not in term or mask[v]&1:left[h:,a,b]=0
    if v not in term or mask[v]&2:right[h:,a,b]=0
    continue
   if v in term:continue
   for h in range(1,6):
    vals=1+left[h-1,a,a+1:b]+right[5,a+1:b,b]
    if not len(vals):continue
    best=int(vals.min())
    if best>=INF:continue
    where=np.flatnonzero(vals==best)+a+1;k=int(where[np.argmin(abs(where-(a+b)/2))]);left[h,a,b]=right[h,a,b]=best;cut[h,a,b]=k
 print('PARSE',n,'new-tree-cost',int(left[5,0,n]),flush=True)
 if left[5,0,n]>=INF:return None
 out=dict(g);need={}
 def gather(a,b,h):
  v=strings[a,b]
  if (v in available and available[v]<=h):return
  if v in need and need[v]<=h:return
  need[v]=h;k=int(cut[h,a,b]);assert k>=0,(v,h)
  gather(a,k,h-1);gather(k,b,5)
 gather(0,n,5)
 def put(a,b,h):
  v=strings[a,b]
  if v not in need:return
  h=need[v];k=int(cut[h,a,b]);assert k>=0
  put(a,k,h-1);put(k,b,5);out[v]=(strings[a,k],strings[k,b])
 put(0,n,5)
 return out
for step in range(20):
 wp,full=evaluate(g);print('CURRENT',len(g),full,flush=True)
 if full[1]<=5:break
 bad=sorted((w for w,(a,b)in g.items()if wp(a)[0]>=5),key=len)
 if not bad:break
 best=None
 for w in bad:
  if len(w)>240:continue
  answer=repair(w,g)
  if answer is None:continue
  _,p=evaluate(answer)
  if p[2]>64:continue
  best=answer;break
 if best is None:break
 g=best
# Remove rules made obsolete by whole-word reparsing.
seen=set()
def visit(w):
 if w in term or w in seen:return
 seen.add(w)
 for x in g[w]:visit(x)
for w in d['roots']+[r['word']for r in d['routes']]:visit(w)
g={w:g[w]for w in seen};wp,p=evaluate(g);d.update(rules_count=len(g),rules=[[w,*ab]for w,ab in sorted(g.items())],properties=list(p),status='ABSTRACT_CANONICAL_ZERO5_REPAIR')
print('FINAL',len(g),p,flush=True);Path(str(source).replace('.json','-parsed.json')).write_text(json.dumps(d,indent=2)+'\n')
