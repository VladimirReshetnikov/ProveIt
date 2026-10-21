from pathlib import Path
from functools import cache
import source_language as s,source_splice as sp,json,itertools,time
P=Path(__file__).resolve().parent
root=s.tree(json.loads((P/'sites215.json').read_text()))
ranges=[('G',479,888),('rho6',888,1171),('rho5',1171,1467),('rho4',1467,1766),('rho3',1766,2062),('rho2',2062,2412),('rho1',2412,2643)]
@cache
def atoms(t):
 if s.leaf(t)or sp.boundary(t[0])!=(0,0,False)or sp.boundary(t[1])!=(0,0,False):return(t,)
 return atoms(t[0])+atoms(t[1])
rows=[sum((atoms(q)for q in sp.closed_forest(root,lo,hi)),())for _,lo,hi in ranges]
oldatoms=sum(rows,())
# Build a scaffold whose negative leaves address interchangeable closed atoms.
slot=0
def scaffold(t,i=0):
 global slot
 j=i+sp.size(t)
 if j<=479 or i>=2643:return t
 if i>=479 and j<=2643 and (s.leaf(t)or sp.boundary(t[0])!=(0,0,False)or sp.boundary(t[1])!=(0,0,False)):
  out=-1-slot;assert t==oldatoms[slot];slot+=1;return out
 assert not s.leaf(t)
 return(scaffold(t[0],i),scaffold(t[1],i+sp.size(t[0])))
scaf=scaffold(root);assert slot==len(oldatoms)
def subst(n,aa):
 if isinstance(n,int):return aa[-n-1]
 if s.leaf(n):return n
 return(subst(n[0],aa),subst(n[1],aa))
assert subst(scaf,oldatoms)==root
@cache
def regswap(n):
 if s.leaf(n):return(n[0],{3:5,5:3}.get(n[1],n[1]))if n[0]in('CI','CD')else n
 return(regswap(n[0]),regswap(n[1]))
best=202;count=0;found=[];hist={};started=time.time()
configs=[(),(1,),(3,5),(1,3,5)]
for cfg in configs:
 variants=[tuple(regswap(a)for a in row)if i in cfg else row for i,row in enumerate(rows)]
 for order in itertools.permutations(range(7)):
  aa=sum((variants[j]for j in order),())
  t=subst(scaf,aa);score=len(sp.nodes(t));hist[score]=hist.get(score,0)+1;count+=1
  if score<best:
   best=score;found=[];print('BEST',best,order,cfg,'seconds',time.time()-started,flush=True)
  if score==best:
   found.append((order,cfg))
   if len(found)<=16:
    m=s.metrics(t);f=P/f'roworder_scaffold_{count}_{score}.json';f.write_bytes(s.compact(s.sites(t)))
    print('SAVE',f.name,order,cfg,m,flush=True)
 print('completedconfig',cfg,'total',count,'best',best,'seconds',time.time()-started,flush=True)
(P/'row_order_scaffold_summary.json').write_text(json.dumps({'method':'Keep the exact K215 binary scaffold, reorder minimal closed atomic components of whole logical row words','orders':count,'minimum_dag':best,'bestresults':found,'histogram':hist,'seconds':time.time()-started},indent=2)+'\n')

