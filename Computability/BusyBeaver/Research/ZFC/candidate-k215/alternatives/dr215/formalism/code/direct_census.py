import argparse,json,sys,itertools,time,hashlib
from pathlib import Path
from functools import lru_cache
ap=argparse.ArgumentParser(description='Exhaustive row-parameter permutations of the exact new DR215 source.')
ap.add_argument('--seed',type=Path,required=True)
ap.add_argument('--exchange-g',action='store_true')
ap.add_argument('--output',type=Path,required=True)
a=ap.parse_args();base=a.seed
a.output.mkdir(parents=True,exist_ok=False)
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'vendor'));import source_language as s
raw=base.read_bytes();assert hashlib.sha256(raw).hexdigest()=='74d21758da7e932de766bee079adf11a7917c03a1957b1111abc6463d70eb332'
rows=json.loads(raw)
if a.exchange_g:
 for row in rows[478:642]:
  if row[1] in ('CI','CD'):row[2]={4:5,5:4}.get(row[2],row[2])
root=s.tree(rows);out=a.output
names=['rho7G','rho6','rho5','rho4','rho3','rho2','rho1']
spans=[(478,887),(887,1170),(1170,1466),(1466,1765),(1765,2061),(2061,2411),(2411,2642)]
perms=list(itertools.permutations([3,4,5]))
# Integer hash-consed source DAG.
ids={};nodes=[]
def intern(n):
 if n not in ids:ids[n]=len(nodes);nodes.append(n)
 return ids[n]
@lru_cache(None)
def code(n):
 if s.leaf(n):return intern(n)
 return intern((code(n[0]),code(n[1])))
@lru_cache(None)
def rename(n,k):
 if s.leaf(n):
  op,r=n
  return (op,perms[k][r-3]) if op in ['CI','CD'] and r in [3,4,5]else n
 return(rename(n[0],k),rename(n[1],k))
@lru_cache(None)
def size(n):return 1 if s.leaf(n)else size(n[0])+size(n[1])
@lru_cache(None)
def closure(i):
 n=nodes[i]
 return (1<<i) if isinstance(n[0],str)else (1<<i)|closure(n[0])|closure(n[1])
# Skeleton entries: constants, six-way choices, branch; children earlier.
skel=[]
def walk(n,lo=0):
 hi=lo+size(n)
 for j,(a,b)in enumerate(spans):
  if a<=lo and hi<=b:
   opts=tuple(code(rename(n,k))for k in range(6));skel.append(('v',j,opts));return len(skel)-1
 if all(hi<=a or lo>=b for a,b in spans):skel.append(('c',code(n)));return len(skel)-1
 assert not s.leaf(n)
 l=walk(n[0],lo);r=walk(n[1],lo+size(n[0]));skel.append(('b',l,r));return len(skel)-1
rootindex=walk(root)
# All fixed closures precomputed before any skeleton instantiations.
fixedmask=0;varmasks=[[0]*6 for _ in range(7)]
for st in skel:
 if st[0]=='c':fixedmask|=closure(st[1])
 elif st[0]=='v':
  for k,i in enumerate(st[2]):varmasks[st[1]][k]|=closure(i)
baseN=len(nodes)
print('skeleton',len(skel),'baseN',baseN,'fixedcount',fixedmask.bit_count(),flush=True)
# New skeleton nodes are never reused in subtree closures; only count deduped ids.
best=s.metrics(root)['dag_nodes'];hits=[];hist={};start=time.monotonic()
for count,choice in enumerate(itertools.product(range(6),repeat=7),1):
 mask=fixedmask
 for j,k in enumerate(choice):mask|=varmasks[j][k]
 vals=[];added=set()
 for st in skel:
  if st[0]=='c':i=st[1]
  elif st[0]=='v':i=st[2][choice[st[1]]]
  else:
   i=intern((vals[st[1]],vals[st[2]]))
   if i<baseN:mask|=1<<i
   else:added.add(i)
  vals.append(i)
 cost=mask.bit_count()+len(added);hist[cost]=hist.get(cost,0)+1
 if cost<best:
  best=cost;hits=[];print('BEST',best,choice,'after',count,'seconds',time.monotonic()-start,flush=True)
 if cost<=best:hits.append((choice,cost))
 if count%50000==0:print('progress',count,'seconds',time.monotonic()-start,'nodes',len(nodes),flush=True)
res={'count':count,'best':best,'histogram':hist,'hits':hits,'seconds':time.monotonic()-start,'method':'Exhaustive 6^7 independent row parameter permutations retaining the literal existing source association.'}
(out/'row_combinations_results.json').write_text(json.dumps(res,indent=2)+'\n')
for z,(choice,cost)in enumerate(hits[:500]):
 rr=[x[:]for x in rows]
 for j,k in enumerate(choice):
  lo,hi=spans[j];mp=dict(zip([3,4,5],perms[k]))
  for i in range(lo,hi):
   if rr[i][1]in ['CI','CD'] and rr[i][2]in mp:rr[i][2]=mp[rr[i][2]]
 new=s.tree(rr);assert s.metrics(new)['dag_nodes']==cost
 (out/f'combo{z:03}.json').write_bytes(s.compact(rr))
print(json.dumps(res,indent=2))
