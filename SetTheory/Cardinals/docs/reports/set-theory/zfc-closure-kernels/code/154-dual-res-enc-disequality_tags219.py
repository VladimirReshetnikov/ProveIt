#!/usr/bin/env python3
"""Integer-DAG sweep of J=4P+1, M=4P+3 with derived equality N(J)."""
from pathlib import Path
import itertools,json,time,collections
import inverse_mp as q
import recompile219 as compiler
s,b,z=q.s,q.b,q.z
BASE=q.W/'K219_Construction_2026-10-20'
ROWS=json.loads((BASE/'machine/sites219.json').read_text());OLD=s.tree(ROWS)
T=b.read_table((BASE/'machine/k219.native.tm').read_bytes())
OUT=q.W/'disequality_tags219';OUT.mkdir(exist_ok=True)
word=tuple(tuple(r[1:])for r in ROWS);iw=q.x.flat(z.MACRO[119])
rs=[];es=[]
for i in range(len(word)-len(iw)+1):
 if word[i:i+len(iw)]!=iw:continue
 j=i+len(iw);k=0
 while j+k<len(word)and word[j+k]==('CI',1):k+=1
 if k==1:rs.append(j)
 if k==3:es.append(j)
assert len(rs)==12 and len(es)==6 and 729 in rs
slots={p+j:(i,j)for i,p in enumerate(es)for j in range(3)}
nodes=[];ids={};info=[]
def intern(n):
 if n in ids:return ids[n]
 i=len(nodes);ids[n]=i;nodes.append(n)
 if isinstance(n[0],str):m=(1,0,0,0)
 else:
  aa,bb=(info[c]for c in n);lead=aa[1]+1
  m=(aa[0]+bb[0],lead,max(lead,aa[2],bb[2]),1+max(aa[3],bb[3]))
 info.append(m);return i
def index(t):return intern(t)if s.leaf(t)else intern((index(t[0]),index(t[1])))
OLDID=index(OLD);CI=index(('CI',1));NEG=index(z.MACRO[218]);CINEG=intern((CI,NEG))
triple=[intern((CI,intern((CI,CI)))),intern((intern((CI,CI)),CI))]
odd=(('CD',5),((('CD',5),('CC',2)),('CH',None)));ODD=index(odd)
fixedlen=len(nodes);fixedids=dict(ids)
def join(a,bb):return bb if a<0 else a if bb<0 else intern((a,bb))
def skeleton(n,lo=0):
 hi=lo+len(q.x.flat(n))
 if 2527<=lo and hi<=2574:return('D',index(n))
 if s.leaf(n):
  if lo in slots:return('E',*slots[lo])
  if lo in rs:return('R',lo==729)
  return('F',index(n))
 if hi<=4598 or lo>=4610:
  if not any(lo<=p<hi for p in slots)and not any(lo<=p<hi for p in rs)and(hi<=2527 or lo>=2574):return('F',index(n))
 if lo==4598:return('O',)
 if 4598<lo and hi<=4610:return('X',)
 return('N',skeleton(n[0],lo),skeleton(n[1],lo+len(q.x.flat(n[0]))))
# Insertion at ordinal4598 consumes the complete old NIP prefix. Descend at
# its first leaf, then delete only the remaining old prefix leaves.
def skel(n,lo=0):
 hi=lo+len(q.x.flat(n))
 if 2527<=lo and hi<=2574:return('D',index(n))
 if 4598<lo and hi<=4610:return('X',)
 if s.leaf(n):
  if lo==4598:return('O',)
  if lo in slots:return('E',*slots[lo])
  if lo in rs:return('R',lo==729)
  return('F',index(n))
 if not any(lo<=p<hi for p in slots)and not any(lo<=p<hi for p in rs)and(hi<=2527 or lo>=2574)and(hi<=4598 or lo>=4610):return('F',index(n))
 return('N',skel(n[0],lo),skel(n[1],lo+len(q.x.flat(n[0]))))
SK=skel(OLD)
def build(sk,keeps,assoc,binder,simple):
 typ=sk[0]
 if typ=='F':return sk[1]
 if typ=='D':return -1 if simple else sk[1]
 if typ=='X':return -1
 if typ=='O':return ODD
 if typ=='E':
  i,j=sk[1:]
  return -1 if keeps[i]!=j else CI if simple and i==5 else CINEG
 if typ=='R':return CI if sk[1]and binder else triple[assoc]
 return join(build(sk[1],keeps,assoc,binder,simple),build(sk[2],keeps,assoc,binder,simple))
def live(root):
 seen={root};todo=[root]
 for i in todo:
  n=nodes[i]
  if isinstance(n[0],str):continue
  for j in n:
   if j not in seen:seen.add(j);todo.append(j)
 return len(seen)
def tree(root):
 memo={}
 def go(i):
  if i in memo:return memo[i]
  n=nodes[i];out=n if isinstance(n[0],str)else(go(n[0]),go(n[1]));memo[i]=out;return out
 return go(root)
start=time.time();hist=collections.Counter();allowed=collections.Counter();best=999;best_allowed=999;records=[];saved=0
for count,(keeps,assoc,binder,simple)in enumerate(itertools.product(itertools.product(range(3),repeat=6),range(2),[False,True],[False,True]),1):
 root=build(SK,keeps,assoc,binder,simple);d=live(root);m=info[root];hist[d]+=1
 row={'keep_J_tag_indices':keeps,'membership_increment_association':assoc,'keep_fresh_binder_at_tag1':binder,'simplify_rho1':simple,'dag_nodes':d,'leaf_occurrences':m[0],'maximum_zero_run':m[2],'maximum_depth':m[3]}
 if d<best:best=d;print('BEST',row,flush=True)
 if m[2]<=6:
  allowed[d]+=1
  if d<best_allowed:best_allowed=d;saved=0;print('BEST_ALLOWED',row,flush=True)
  if d==best_allowed and saved<8:
   tt=tree(root);dd=OUT/f'case{count}';dd.mkdir(exist_ok=True);rr=s.sites(tt)
   assert s.graph_arithmetic(rr)[0]==s.graph_intervals(rr)
   (dd/'sites.json').write_bytes(s.compact(rr))
   if d<=211:
    try:
     U,meta=compiler.compile_tree(T,OLD,tt,extend_direct=True);row['compiler']=meta;(dd/'candidate.tm').write_bytes(b.table_bytes(U))
    except Exception as exc:row['error']=repr(exc)
   (dd/'receipt.json').write_text(json.dumps(row,indent=2)+'\n');records.append(row);saved+=1
 if count%500==0:
  nodes[fixedlen:]=[];info[fixedlen:]=[];ids.clear();ids.update(fixedids)
  print('PROGRESS',count,'seconds',round(time.time()-start,2),flush=True)
payload={'tested':count,'minimum_DAG':best,'minimum_DAG_zero6':best_allowed,'histogram':dict(hist),'zero6_histogram':dict(allowed),'records':records,'seconds':time.time()-start,'scope':'Constructor formula semantics and runtime require separate proof; two CFG resolvers agree'}
(OUT/'summary.json').write_text(json.dumps(payload,indent=2)+'\n')
print('DONE',count,best,best_allowed,flush=True)
