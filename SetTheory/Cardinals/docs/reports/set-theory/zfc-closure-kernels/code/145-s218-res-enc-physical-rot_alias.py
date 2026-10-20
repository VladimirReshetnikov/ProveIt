from collections import defaultdict
import sys
# Set PYTHONPATH to the pinned K221 portable directory; see README.md.
import source_language as s,build221 as b

def rotations(T,rows,maxzr=6):
 tree=s.tree(rows);Ti={k:(w,1 if d=='R'else -1,z)for k,(w,d,z)in T.items()}
 try:g,p=b.decoder_map(Ti,tree)
 except Exception:return
 for q in sorted(g):
  if any(T[q,c][:2]!=(c,'R')for c in(0,1)):continue
  for direction,bit in [('L',1),('R',0)]:
   r=T[q,bit][2]
   if r not in g or r==q or any(T[r,c][:2]!=(c,'R')for c in(0,1)):continue
   if set(p[r])!={x+str(bit)for x in p[q]}:continue
   good=True
   for X in g[q]:
    if s.leaf(X[bit]):good=False;break
    if bit:A,(B,C)=X
    else:(A,B),C=X
    if s.boundary(A)[0]or s.boundary(C)[1]:good=False;break
   if not good:continue
   N=T.copy()
   if bit:
    N[q,0]=(0,'R',r);N[q,1]=(1,'R',T[r,1][2]);N[r,0]=(0,'R',T[q,0][2]);N[r,1]=(1,'R',T[r,0][2])
   else:
    N[q,0]=(0,'R',T[r,0][2]);N[q,1]=(1,'R',r);N[r,0]=(0,'R',T[r,1][2]);N[r,1]=(1,'R',T[q,1][2])
   selected=set(p[q])
   def rec(n,path=''):
    if s.leaf(n):return n
    nn=(rec(n[0],path+'0'),rec(n[1],path+'1'))
    if path in selected:
     if bit:A,(B,C)=nn;nn=((A,B),C)
     else:(A,B),C=nn;nn=(A,(B,C))
    return nn
   new=rec(tree);nr=s.sites(new);zr=s.metrics(new)['maximum_zero_run']
   if zr>maxzr:continue
   # Reconfirm every role, including path-dependent aliases.
   try:b.decoder_map({k:(w,1 if d=='R'else -1,z)for k,(w,d,z)in N.items()},new)
   except Exception:continue
   yield f'{direction}_{q}_{r}_alias{len(g[q])}',N,nr,zr
