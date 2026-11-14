"""Optimize the actual reusable grammar rather than old-node occurrence cost.

The fixed base contains only nodes forced by unchanged source fragments and
indecomposable control atoms. Non-base nodes have weight 1 / phrase frequency.
Equal phrases have deterministic parses, so this approximates unique DAG cost.
The final result is checked by exact source metrics and primitive CFG equality.
"""
from pathlib import Path
import sys,json,functools,time,hashlib,collections
sys.path.insert(0,str(Path(__file__).resolve().parent))
import build_fixed_cover as f
s=f.s;br=f.br
prefix=br.closed_forest(f.old_tree,158,f.LO)
anchors=set(prefix)
@functools.cache
def flat(t):
 if t in anchors or s.leaf(t) or s.boundary(t[0])!=(0,0,False) or s.boundary(t[1])!=(0,0,False):return (t,)
 return flat(t[0])+flat(t[1])
def collect(t,d):
 if t in d:return
 d.add(t)
 if not s.leaf(t):collect(t[0],d);collect(t[1],d)
forced0=set()
def preserve(t,offset=0):
 end=offset+br.size(t)
 if end<=f.LO or offset>=f.HI:collect(t,forced0);return
 if not s.leaf(t):preserve(t[0],offset);preserve(t[1],offset+br.size(t[0]))
preserve(f.old_tree)
for name in sys.argv[1:]:
 names=f.W[name];atoms=[x for t in prefix+[f.M[x] for x in names] for x in flat(t)]
 forced=set(forced0)
 for t in atoms:collect(t,forced)
 ids={};trees=[];lzero=[];depth=[];maxzero=[]
 def intern(t):
  if t in ids:return ids[t]
  if s.leaf(t):z=h=m=0
  else:
   a,b=map(intern,t);z=lzero[a]+1;h=max(depth[a],depth[b])+1;m=max(maxzero[a],maxzero[b],z)
  i=len(trees);ids[t]=i;trees.append(t);lzero.append(z);depth.append(h);maxzero.append(m);return i
 known={}
 for t in forced:
  if s.boundary(t)==(0,0,False):
   phrase=tuple(intern(x) for x in flat(t));known.setdefault(phrase,[]).append(intern(t))
 word=tuple(intern(x) for x in atoms);n=len(word)
 freq=collections.Counter(word[i:j] for i in range(n) for j in range(i+1,n+1))
 dp=[[None]*(n+1) for _ in range(n)];t0=time.monotonic()
 print(name,'atoms',n,'forced_nodes',len(forced),flush=True)
 for length in range(1,n+1):
  for i in range(n-length+1):
   j=i+length;phrase=word[i:j];best=[None]*7;unit=1/freq[phrase]
   for node in known.get(phrase,[]):
    if maxzero[node]<=6 and depth[node]<=46:
     z=lzero[node];value=(0,depth[node],node)
     if best[z] is None or value[:2]<best[z][:2]:best[z]=value
   if length==1:
    node=word[i];z=lzero[node];assert maxzero[node]<=6
    best[z]=(0,depth[node],node)
   for k in range(i+1,j):
    left=dp[i][k];right=dp[k][j];rb=min((x for x in right if x is not None),default=None)
    if rb is None:continue
    for p in range(6):
     a=left[p]
     if a is None:continue
     z=p+1;c=a[0]+rb[0]+unit;h=max(a[1],rb[1])+1
     if h>46:continue
     if best[z] is not None and (round(c,10),h)>=(round(best[z][0],10),best[z][1]):continue
     node=intern((trees[a[2]],trees[rb[2]]));best[z]=(c,h,node)
   assert any(x is not None for x in best),(i,j)
   dp[i][j]=best
  if length%50==0:print('length',length,'seconds',round(time.monotonic()-t0,1),flush=True)
 choices=[]
 for value in dp[0][n]:
  if value is None or lzero[value[2]]>=6:continue
  tree=s.replace(f.old_tree,'001100111',(trees[value[2]],('CB',1)))
  m=s.metrics(tree)
  if m['maximum_zero_run']<=6 and m['maximum_depth']<=56:choices.append((m['dag_nodes'],m['maximum_depth'],value,tree))
 assert choices
 choice=min(choices,key=lambda x:x[:2]);tree=choice[-1];rows=s.sites(tree);g,checks=s.graph_arithmetic(rows)
 assert g==s.graph_intervals(rows)
 assert g==s.graph_intervals(json.loads((f.OUT/(name+'.sites.json')).read_text()))
 assert rows[:137]==f.old_sites[:137]
 raw=s.compact(rows);(f.OUT/(name+'_weighted.sites.json')).write_bytes(raw)
 (f.OUT/(name+'_weighted.tree.json')).write_text(json.dumps(tree,separators=(',',':'))+'\n')
 receipt={'metrics':s.metrics(tree),'source_sha256':hashlib.sha256(raw).hexdigest(),
   'same_primitive_cfg_as_audited_variant':True,'startup_137_sites_equal':True,
   'weighted_nonforced_node_cost':choice[-2][0],'closed_atoms':n,'forced_nodes':len(forced),
   'seconds':time.monotonic()-t0,'candidate_metrics':[x[:2] for x in choices],
   'scope':'Closed-factor reassociation; forced base and reciprocal phrase-frequency weights.'}
 (f.OUT/(name+'_weighted.json')).write_text(json.dumps(receipt,indent=2)+'\n')
 print(name,json.dumps(receipt),flush=True)
