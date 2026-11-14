"""Closed-factor DP using all existing DAG chunks; final exact CFG audit required."""
from pathlib import Path
import sys,json,functools,time,hashlib
sys.path.insert(0,str(Path(__file__).resolve().parent))
import build_fixed_cover as f
s=f.s;br=f.br
prefix=f.br.closed_forest(f.old_tree,158,f.LO)
anchors=set(prefix)
anchored='--anchor-direct' in sys.argv
if anchored:anchors.update(f.M[x] for x in ['n18','rleft0','rleft1','rright0','rright1','qleft0','qleft1'])
@functools.cache
def flat(t):
 if t in anchors or s.leaf(t) or s.boundary(t[0])!=(0,0,False) or s.boundary(t[1])!=(0,0,False):return (t,)
 return flat(t[0])+flat(t[1])
ids={};trees=[];children=[];lzero=[];depth=[];maxzero=[]
def intern(t):
 if t in ids:return ids[t]
 if s.leaf(t):ch=None;z=h=m=0
 else:
  a,b=map(intern,t);ch=(a,b);z=lzero[a]+1;h=max(depth[a],depth[b])+1;m=max(maxzero[a],maxzero[b],z)
 i=len(trees);ids[t]=i;trees.append(t);children.append(ch);lzero.append(z);depth.append(h);maxzero.append(m);return i
oldid=intern(f.old_tree)
known={}
for t in f.old_nodes:
 if s.boundary(t)==(0,0,False):
  word=tuple(intern(x) for x in flat(t));known.setdefault(word,[]).append(intern(t))
maxwidth=max(map(len,known))
for name,names in f.W.items():
 if len(sys.argv)>1 and name not in sys.argv[1:]:continue
 atoms=[x for t in prefix+[f.M[x] for x in names] for x in flat(t)]
 word=tuple(intern(x) for x in atoms);n=len(word)
 print(name,'atoms',n,'knownwidth',maxwidth,flush=True)
 dp=[[None]*(n+1) for _ in range(n)]
 hits=0;t0=time.monotonic()
 # each p-position holds (new occurrence count, height, id); zero count bound6.
 for length in range(1,n+1):
  for i in range(n-length+1):
   j=i+length;best=[None]*7
   candidates=known.get(word[i:j],[]) if length<=maxwidth else []
   if length==1:candidates=candidates+[word[i]]
   for node in candidates:
    if maxzero[node]<=6 and depth[node]<=46:
     z=lzero[node];value=(0,depth[node],node)
     if best[z] is None or value[:2]<best[z][:2]:best[z]=value
   # Every parse may improve only an unfilled/positive-cost leading-prefix class.
   for k in range(i+1,j):
    left=dp[i][k];right=dp[k][j]
    rb=min((x for x in right if x is not None),default=None)
    if rb is None:continue
    for p in range(6):
     a=left[p]
     if a is None:continue
     z=p+1;c=a[0]+rb[0]+1;h=max(a[1],rb[1])+1
     if h>46:continue
     if best[z] is not None and (c,h)>=best[z][:2]:continue
     pair=(trees[a[2]],trees[rb[2]]);node=intern(pair)
     assert maxzero[node]<=6 and lzero[node]==z
     best[z]=(c,h,node)
   assert any(x is not None for x in best),(i,j)
   dp[i][j]=best
  if length%50==0:print('length',length,'seconds',round(time.monotonic()-t0,1),flush=True)
 choices=[]
 for value in dp[0][n]:
  if value is None:continue
  t=trees[value[2]]
  if lzero[value[2]]>=6:continue
  repl=(t,('CB',1));tree=s.replace(f.old_tree,'001100111',repl)
  metric=s.metrics(tree)
  if metric['maximum_zero_run']>6 or metric['maximum_depth']>56:continue
  choices.append((metric['dag_nodes'],metric['maximum_depth'],metric['maximum_zero_run'],value,tree))
 assert choices,name
 choice=min(choices,key=lambda x:x[:3]);tree=choice[-1];rows=s.sites(tree);g,checks=s.graph_arithmetic(rows)
 assert g==s.graph_intervals(rows)
 original_variant=json.loads((f.OUT/(name+'.sites.json')).read_text())
 assert g==s.graph_intervals(original_variant)
 assert rows[:137]==f.old_sites[:137]
 suffix='_anchored' if anchored else '_optimized'
 raw=s.compact(rows);p=f.OUT/(name+suffix+'.sites.json');p.write_bytes(raw)
 (f.OUT/(name+suffix+'.tree.json')).write_text(json.dumps(tree,separators=(',',':'))+'\n')
 receipt={'metrics':s.metrics(tree),'source_sha256':hashlib.sha256(raw).hexdigest(),
          'same_primitive_cfg_as_audited_variant':True,'startup_137_sites_equal':True,
          'dp_new_node_occurrence_bound':choice[-2][0],'closed_atoms':n,'seconds':time.monotonic()-t0,
          'candidate_metrics':[x[:3] for x in choices],'scope':'Closed-factor reassociation only; exact CFG identity checked.'}
 (f.OUT/(name+('_anchored_optimization' if anchored else '_optimization')+'.json')).write_text(json.dumps(receipt,indent=2)+'\n')
 print(name,json.dumps(receipt),flush=True)
