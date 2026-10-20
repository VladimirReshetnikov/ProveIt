import json,functools,collections
from pathlib import Path
exec(open('/tmp/k219_probe.py').read().split('# finite Cartesian')[0])
N=9
ID=tuple(tuple(int(i==j) for j in range(N))+ (0,) for i in range(N))
def compose(a,b): # execute a then b
 return tuple(tuple(sum(b[i][k]*a[k][j] for k in range(N))+(b[i][N] if j==N else 0) for j in range(N+1)) for i in range(N))
@functools.lru_cache(None)
def localg(t):
 if leaf(t):
  op,r=t;return ((op,r,(-1,) if op=='CI' else (-2,-1) if op=='CD' else (-2*r,) if op=='CB' else (-2*r-1,) if op=='CC' else ()),)
 aa,bb=localg(t[0]),localg(t[1]);la=len(aa)
 def tr(q,side):
  if q>=0:return q+(la if side else 0)
  if side==0:
   if q==-1:return la
   if q%2==0:return -1 if q==-2 else q+2
   return q
  if q < -1 and q%2:return 0 if q==-3 else q+2
  return q
 return tuple((o,r,tuple(tr(q,0) for q in ts)) for o,r,ts in aa)+tuple((o,r,tuple(tr(q,1) for q in ts)) for o,r,ts in bb)
@functools.lru_cache(None)
def affine(t):
 if leaf(t):
  if t[0]!='CI':return None
  a=[list(r) for r in ID];a[t[1]][N]+=1;return tuple(map(tuple,a))
 a,b=affine(t[0]),affine(t[1])
 if a is not None and b is not None:return compose(a,b)
 gg=localg(t)
 op,r,ts=gg[0]
 if op!='CD' or ts[0]!=-1:return None
 pc=ts[1];seen=set();incs=[0]*N
 while pc!=0:
  if pc<0 or pc in seen:return None
  seen.add(pc);op,q,ts=gg[pc]
  if op=='CI':incs[q]+=1
  elif op not in ('CB','CC'):return None
  pc=ts[0]
 if incs[r]:return None
 a=[list(row) for row in ID];a[r]=[0]*(N+1)
 for s in range(N):a[s][r]+=incs[s]
 return tuple(map(tuple,a))
nodes=[];seen=set()
def visit(t):
 if t in seen:return
 seen.add(t)
 if not leaf(t):visit(t[0]);visit(t[1])
 nodes.append(t)
visit(tree)
def replace(t,old,new):return new if t==old else t if leaf(t) else (replace(t[0],old,new),replace(t[1],old,new))
def size(t):
 ss=set()
 def go(t):
  if t in ss:return
  ss.add(t)
  if not leaf(t):go(t[0]);go(t[1])
 go(t);return len(ss)
groups=collections.defaultdict(list)
for i,t in enumerate(nodes):
 m=affine(t)
 if m is not None:groups[m].append(i)
print('affine',sum(map(len,groups.values())),'groups',len(groups),'duplicates',[v for v in groups.values() if len(v)>1])
hits=[]
for ids in groups.values():
 for i in ids:
  for j in ids:
   if i==j:continue
   z=replace(tree,nodes[i],nodes[j]);score=size(z)
   if score<=206:
    rec={'kind':'existing_affine','i':i,'j':j,'score':score,'old':nodes[i],'new':nodes[j],'sites':leaves(z)};hits.append(rec);print({k:v for k,v in rec.items() if k not in ('sites','old','new')})
for i,t in enumerate(nodes):
 if leaf(t):continue
 a,b=t;ma,mb=affine(a),affine(b)
 if ma is not None and mb is not None and compose(ma,mb)==compose(mb,ma):
  m=(b,a);score=size(replace(tree,t,m))
  if score<=206:
   rec={'kind':'commute_affine','i':i,'score':score,'old':t,'new':m,'sites':leaves(replace(tree,t,m))};hits.append(rec);print({k:v for k,v in rec.items() if k not in ('sites','old','new')})
Path('/tmp/k219-affine-result.json').write_text(json.dumps({'affine_nodes':sum(map(len,groups.values())),'groups':len(groups),'hits':hits},indent=2)+'\n')
