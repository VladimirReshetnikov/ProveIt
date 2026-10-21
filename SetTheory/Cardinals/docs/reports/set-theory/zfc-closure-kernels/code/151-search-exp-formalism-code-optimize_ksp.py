import json,sys,functools,collections,itertools,random
from pathlib import Path
from checkpoint_paths import OUTPUT as HERE
from checkpoint_paths import BASELINE as p, PORTABLE
sys.path.insert(0,str(PORTABLE));import source_language as s
import measure as m
T=s.tree(json.loads((p/'sites218.json').read_text())); AA=json.loads((p/'decoder_allocation.json').read_text());q=lambda i:s.subtree(T,next(iter(AA[str(i)].values()))[0])
push=q(98)[0];inc=('CI',1);imp=q(90)
mac={'A':q(98),'B':q(12),'C':q(166),'I':imp,'F':(push,inc),'T':push,'R':(imp,inc),'Q':(imp,(inc,inc)),'E':(imp,((inc,inc),inc))}
# read4 is the exact closed subtree/forest at original positions161:194
# Search all existing closed nodes whose word is the 33-leaf read, otherwise graft its closed pieces.
word=m.flat(T)
def nodes(t):return set([t])if s.leaf(t)else set([t])|nodes(t[0])|nodes(t[1])
allnodes=nodes(T)
for n in allnodes:
 if m.flat(n)==word[161:194]:mac['U']=n;break
else:
 forest=[]
 def collect(t,lo=0):
  hi=lo+len(m.flat(t))
  if hi<=161 or lo>=194:return
  if 161<=lo and hi<=194:
   assert s.boundary(t)==(0,0,False),(lo,hi,s.boundary(t))
   forest.append(t);return
  collect(t[0],lo);collect(t[1],lo+len(m.flat(t[0])))
 collect(T);mac['U']=m.serial(forest)
 assert m.flat(mac['U'])==word[161:194]

K='A B A I I'.split();S='A B C I I A B I A C I I I'.split();DNE='A F I F I A I'.split();QS='A C Q F I F I A C Q I'.split()
def AND(a,b):return a+b+['F','I','I','F','I']
# DAG interning cuts repeated tuple hashing out of the DP.
ids={};trees=[];children=[]
def intern(t):
 if t in ids:return ids[t]
 if s.leaf(t):cc=()
 else:cc=(intern(t[0]),intern(t[1]))
 k=len(trees);ids[t]=k;trees.append(t);children.append(cc);return k
root=intern(T)
@functools.cache
def closure(k):
 return frozenset([k]) if not children[k] else frozenset([k])|closure(children[k][0])|closure(children[k][1])
# hole gets replaced, base is retained subtrees of the context, excluding nodes containing hole.
hole=('XX',0)
skeleton=m.splice(s,T,135,486,hole)
base=frozenset(intern(n)for n in nodes(skeleton)if hole not in m.flat(n))
closed_by_word=collections.defaultdict(list)
for n in allnodes:
 if s.boundary(n)==(0,0,False):closed_by_word[m.flat(n)].append(intern(n))

@functools.cache
def shape(k):
 if not children[k]:return (0,0,0)
 a,b=map(shape,children[k]);return (1+max(a[0],b[0]),1+a[1],max(a[2],b[2],1+a[1]))

def optimize(tokens,beam=4,bonus=None):
 bonus=bonus or set()
 nn=len(tokens);dp={};ww=[m.flat(mac[x])for x in tokens]
 for length in range(1,nn+1):
  for i in range(nn-length+1):
   j=i+length;w=sum(ww[i:j],());cands=set(closed_by_word.get(w,[]))
   if length==1:cands.add(intern(mac[tokens[i]]))
   for cut in range(i+1,j):
    for l in dp[i,cut]:
     for r in dp[cut,j]:cands.add(intern((trees[l],trees[r])))
   def rank(k):
    cc=closure(k)-base
    return (len(cc-bonus),len(cc),shape(k)[2],shape(k)[0],k)
   dp[i,j]=sorted(cands,key=rank)[:beam]
 return [trees[k]for k in dp[0,nn]]


P='A B I A I A I'.split()
families=[('KSPout',K+S+P),('KSPand',AND(K,AND(S,P)))]
results=[]
for name,ws in families:
 best=None
 for candidate in optimize(ws,4):
  tree=m.splice(s,T,135,486,candidate);met=s.metrics(tree);r={'name':name,'metrics':met,'tokens':ws}
  key=(met['dag_nodes'],met['maximum_zero_run'],met['maximum_depth'])
  if best is None or key<best[0]:best=(key,tree,r)
 _,tree,r=best;r['cfg']='PASS' if s.graph_arithmetic(s.sites(tree))[0]==s.graph_intervals(s.sites(tree)) else 'FAIL'
 print(r,flush=True);results.append(r);(HERE/(name+'.opt.sites.json')).write_bytes(s.compact(s.sites(tree)))
(HERE/'ksp_results.json').write_text(json.dumps(results,indent=2)+'\n')
