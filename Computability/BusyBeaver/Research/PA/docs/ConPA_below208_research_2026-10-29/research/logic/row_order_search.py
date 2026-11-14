"""All7! axiom-row orders, with bounded closed-factor association synthesis.
Each order receives a deterministic beam1 association per five retained slots.
This exhausts row orders within this heuristic, NOT all binary associations.
"""
import sys,json,itertools,time,collections
from pathlib import Path
from paths import OUT
import model as e
s,sp=e.s,e.sp
regions=[('G',478,887),('rho6',887,1170),('rho5',1170,1466),('rho4',1466,1765),('rho3',1765,2061),('rho2',2061,2411),('rho1',2411,2642)]
rowunits=[[e.intern(n)for n in sp.closed_forest(e.old,lo,hi)]for _,lo,hi in regions]
whole=sp.closed_forest(e.old,478,2642);groups=[e.intern(n)for n in whole]
oldnodes=list(e.nodes);oldshapes=list(e.shapes);oldids=dict(e.ids);oldroot=e.intern(e.old)
allpaths={}
def paths(n,p='',lo=0):
 allpaths[lo,lo+sp.size(n)]=p
 if not s.leaf(n):paths(n[0],p+'0',lo);paths(n[1],p+'1',lo+sp.size(n[0]))
paths(e.old)
slotpaths=[];offset=478
for n in whole:slotpaths.append(allpaths[offset,offset+sp.size(n)]);offset+=sp.size(n)
counts=[];units=sum(rowunits,[]);u=0
for n in whole:
 total=0;count=0
 while total<sp.size(n):total+=sp.size(e.expand(units[u]));u+=1;count+=1
 assert total==sp.size(n);counts.append(count)
assert u==len(units)
# The fixed roots are all atomic units plus all subtrees outside the five slots.
fixedroots=set(units);prefixes={p[:j]for p in slotpaths for j in range(len(p))}
def outside(k,p=''):
 if p in slotpaths:return
 if p not in prefixes:fixedroots.add(k);return
 a,b=oldnodes[k];outside(a,p+'0');outside(b,p+'1')
outside(oldroot)
base_sets=[]
for k,n in enumerate(oldnodes):base_sets.append(frozenset({k})if isinstance(n[0],str)else frozenset({k})|base_sets[n[0]]|base_sets[n[1]])
fixed=frozenset().union(*(base_sets[k]for k in fixedroots))
out=OUT/'row_orders';out.mkdir(exist_ok=True);best=999;records=[];census=collections.Counter();started=time.monotonic()
for order in itertools.permutations(range(7)):
 nodes=oldnodes.copy();shapes=oldshapes.copy();ids=oldids.copy();sets=base_sets.copy();cost=[len(x-fixed)for x in sets]
 def pair(a,b):
  key=a,b
  if key in ids:return ids[key]
  k=len(nodes);ids[key]=k;nodes.append(key);st=frozenset({k})|sets[a]|sets[b];sets.append(st);cost.append(len(st-fixed))
  da,za,ma=shapes[a];db,zb,mb=shapes[b];shapes.append((1+max(da,db),1+za,max(1+za,ma,mb)));return k
 def associate(seq):
  n=len(seq);dp={(i,i+1):seq[i]for i in range(n)}
  for length in range(2,n+1):
   for lo in range(n-length+1):
    hi=lo+length;bestkey=None;bestpair=None
    for mid in range(lo+1,hi):
     a,b=dp[lo,mid],dp[mid,hi];existing=ids.get((a,b));c=len((sets[a]|sets[b])-fixed)+(0 if existing in fixed else 1)
     da,za,ma=shapes[a];db,zb,mb=shapes[b];key=(c,max(1+za,ma,mb),1+max(da,db),mid)
     if bestkey is None or key<bestkey:bestkey=key;bestpair=a,b
    dp[lo,hi]=pair(*bestpair)
  return dp[0,n]
 seq=sum((rowunits[i]for i in order),[]);replacements={};off=0
 for p,n in zip(slotpaths,counts):replacements[p]=associate(seq[off:off+n]);off+=n
 def rebuild(k,p=''):
  if p in replacements:return replacements[p]
  if p not in prefixes:return k
  a,b=nodes[k];return pair(rebuild(a,p+'0'),rebuild(b,p+'1'))
 root=rebuild(oldroot);val=len(sets[root]);census[val]+=1
 if val<best or(val==best and len(records)<12):
  best=min(best,val)
  def expand(k):
   n=nodes[k];return n if isinstance(n[0],str)else(expand(n[0]),expand(n[1]))
  tree=expand(root);rows=s.sites(tree);g,_=s.graph_arithmetic(rows);assert g==s.graph_intervals(rows);assert sp.boundary(tree)==(0,0,True)
  name=f'order{val}_'+''.join(map(str,order));(out/(name+'.json')).write_text(json.dumps(rows,separators=(',',':'))+'\n')
  rec={'name':name,'order':order,'metrics':s.metrics(tree),'source_slots':slotpaths,'slot_atomic_counts':counts};records.append(rec);print('BEST',rec,flush=True)
 if sum(census.values())%500==0:print('PROGRESS',sum(census.values()),'best',best,'seconds',round(time.monotonic()-started,2),flush=True)
result={'status':'BOUNDED_ROW_ORDER_ASSOCIATION_CENSUS','orders':sum(census.values()),'row_regions':regions,'fixed_nodes':len(fixed),'slot_counts':counts,'association':'beam1 substring dynamic programming minimizing nonfixed distinct-node union, with deterministic zero-run/depth tie breaks; no exhaustive association claim','best_dag':best,'histogram':dict(census),'records':records,'seconds':time.monotonic()-started}
(out/'census.json').write_text(json.dumps(result,indent=2)+'\n');print('COMPLETE',best,result['seconds'],flush=True)
