import json,sys,random
from pathlib import Path
from functools import lru_cache
sys.path.insert(0,str(Path(__file__).parent));import source_language as L
r=json.load(open(Path(sys.argv[1])/'machine/sites.json'));root=L.tree(r)
def at(n,p):
 for c in p:n=n[int(c)]
 return n
root=L.replace(root,'001101110',at(root,'0011011101'));root=L.replace(root,'1110011',at(root,'11100111'))
def nodes(t):
 s=set()
 def v(n):
  if n in s:return
  s.add(n)
  if not L.leaf(n):v(n[0]);v(n[1])
 v(t);return s
@lru_cache(None)
def replaceall(t,old,new):
 if t==old:return new
 if L.leaf(t):return t
 return replaceall(t[0],old,new),replaceall(t[1],old,new)
beam=[root];seen={root};rng=random.Random(7)
for depth in range(8):
 todo=[]
 for t in beam:
  for n in sorted(nodes(t),key=repr):
   if L.leaf(n):continue
   for side in (0,1):
    if L.leaf(n[side]):continue
    if side==0:(a,b),c=n;nn=(a,(b,c))
    else:a,(b,c)=n;nn=((a,b),c)
    if any(L.boundary(x)!=(0,0,False)for x in(a,b,c)):continue
    tt=replaceall(t,n,nn)
    if tt in seen:continue
    seen.add(tt);todo.append((len(nodes(tt)),rng.random(),tt))
 todo.sort();beam=[x[2]for x in todo[:8]];print(depth,len(seen),[(x[0],L.metrics(x[2])['maximum_zero_run'])for x in todo[:8]],flush=True)
 if not beam:break
 if todo[0][0]<197:
  Path(sys.argv[2]).write_text(json.dumps(L.sites(beam[0])));break
 replaceall.cache_clear()
