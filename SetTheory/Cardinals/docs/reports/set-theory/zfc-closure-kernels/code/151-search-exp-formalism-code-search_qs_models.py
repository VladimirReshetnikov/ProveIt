"""Finite upset-algebra normal modalities, seriality + rho6, seeking unstable Q range."""
import itertools,json,time
from pathlib import Path
start=time.time();seen=0;models=0
for n in range(1,6):
 edges=[(i,j)for i in range(n)for j in range(i+1,n)];posets=set()
 for bits in range(1<<len(edges)):
  up=[1<<i for i in range(n)]
  for k,(i,j)in enumerate(edges):
   if bits>>k&1:up[i]|=1<<j
  for i in reversed(range(n)):
   for j in range(i+1,n):
    if up[i]>>j&1:up[i]|=up[j]
  posets.add(tuple(up))
 for up in posets:
  U=[a for a in range(1<<n)if all(not(a>>i&1)or up[i]&~a==0 for i in range(n))]
  neg={a:sum((1<<i)for i in range(n)if not(up[i]&a))for a in U}
  if all(neg[neg[a]]==a for a in U):continue
  options=U[1:];sets=[0]*n
  def rec(k):
   global seen,models
   if k==n:
    seen+=1
    q={a:sum((1<<i)for i in range(n)if not(sets[i]&~a))for a in U}
    if any(neg[q[neg[q[a]]]]&~a for a in U):return
    models+=1
    for a in U:
     if neg[neg[q[a]]]&~q[a]:
      out={'n':n,'up':up,'upsets':U,'accessibility_upsets':sets.copy(),'Q':q,'witness':a,'counts':[seen,models],'seconds':time.time()-start}
      print('FOUND',out,flush=True);Path(__file__).with_name('qs_countermodel.json').write_text(json.dumps(out,indent=2)+'\n');raise SystemExit
    return
   for x in options:
    if any((up[i]>>k&1)and(x&~sets[i])for i in range(k)):continue
    sets[k]=x;rec(k+1)
  rec(0)
 print('DONE',n,'posets',len(posets),'maps',seen,'models',models,'seconds',round(time.time()-start,2),flush=True)
