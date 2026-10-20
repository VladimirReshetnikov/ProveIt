from collections import defaultdict
import sys
# Set PYTHONPATH to the pinned K221 portable directory; see README.md.
import source_language as s,build221 as b

def rotations(T, rows, maxzr=6):
 Ti={k:(w,1 if d=='R'else -1,z)for k,(w,d,z)in T.items()}
 tree=s.tree(rows)
 try:g,p=b.decoder_map(Ti,tree)
 except Exception:return
 bynode=defaultdict(set)
 for q,ns in g.items():
  for n in ns:bynode[n].add(q)
 def state(n):
  qs=bynode.get(n,set())
  if len(qs)!=1:return None
  q=next(iter(qs))
  return q if len(g[q])==1 else None
 parents=defaultdict(set);seen=set()
 def walk(n):
  if s.leaf(n)or n in seen:return
  seen.add(n)
  for c in n:parents[c].add(n);walk(c)
 walk(tree)
 for X in sorted(seen,key=repr):
  q=state(X)
  if q is None or any(T[q,c][:2]!=(c,'R')for c in(0,1)):continue
  for direction in('L','R'):
   Y=X[1]if direction=='L'else X[0]
   if s.leaf(Y)or parents[Y]!={X}:continue
   r=state(Y)
   if r is None or q==r or any(T[r,c][:2]!=(c,'R')for c in(0,1)):continue
   if direction=='L': A,(B,C)=X; Z=(A,B); Nnode=(Z,C)
   else:(A,B),C=X;Z=(B,C);Nnode=(A,Z)
   if s.boundary(A)[0]or s.boundary(C)[1]:continue
   z=state(Z)if Z in seen else r
   if z is None:continue
   N=dict(T)
   if direction=='L':
    N[q,0]=(0,'R',z);N[q,1]=(1,'R',T[r,1][2])
    if z==r:N[r,0]=(0,'R',T[q,0][2]);N[r,1]=(1,'R',T[r,0][2])
   else:
    N[q,0]=(0,'R',T[r,0][2]);N[q,1]=(1,'R',z)
    if z==r:N[r,0]=(0,'R',T[r,1][2]);N[r,1]=(1,'R',T[q,1][2])
   def replace(n):
    if n==X:return Nnode
    return n if s.leaf(n)else(replace(n[0]),replace(n[1]))
   nt=replace(tree);nr=s.sites(nt)
   zr=max(len(zr)for p,*_ in nr for zr in p.split('1'))
   if zr>maxzr:continue
   reach={0};todo=[0]
   for aq in todo:
    for c in(0,1):
     zz=N[aq,c][2]
     if zz!=254 and zz not in reach:reach.add(zz);todo.append(zz)
   N={k:v for k,v in N.items()if k[0]in reach}
   yield f'{direction}_{q}_{r}_use{z}',N,nr,zr
