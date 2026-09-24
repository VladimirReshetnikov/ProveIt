"""Discover finite hull certificates. Qhull proposes; integer determinants certify."""
from pathlib import Path
from itertools import combinations
import json
import numpy as np
from scipy.spatial import ConvexHull
D=Path(__file__).resolve().parents[1]/'data'
U=((1,0,2),(-1,0,2),(0,1,0));V=((0,1,0),(0,-1,0),(1,0,0))
def mv(a,v):return tuple(sum(x*y for x,y in zip(row,v)) for row in a)
def rowmul(v,a):return tuple(sum(v[i]*a[i][j] for i in range(3)) for j in range(3))
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def det(a,b,c):return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])
def cert_tetra(p,a,b,c):
 d=det(a,b,c)
 if not d:return False
 ns=[det(p,b,c),det(a,p,c),det(a,b,p)]
 if d<0:d=-d;ns=[-x for x in ns]
 return min(ns)>=0 and sum(ns)<=d

def certify_removed(p,vs,faces,arr):
 pfloat=np.array(p,dtype=float)/SCALE
 opts=[]
 for tri in faces:
  a=arr[list(tri)].T
  if abs(np.linalg.det(a))<1e-14:continue
  w=np.linalg.solve(a,pfloat)
  scores=list(w)+[1-sum(w)]
  if min(scores)>-1e-9:opts.append((min(scores),tri))
 opts.sort(reverse=True)
 for _,t in opts:
  if cert_tetra(p,*(vs[i] for i in t)):return list(map(int,t))
 for t in combinations(range(len(vs)),3):
  if cert_tetra(p,*(vs[i] for i in t)):return list(t)
 raise ValueError('uncontained vertex')

base=(1,-1,1)
prev=[base,tuple(-x for x in base)]
hulls=[prev]
stages=[]
for m in range(3,403):
 points=[mv(T,v) for T in (U,V) for v in prev]
 if m==3:
  keep=list(range(len(points)));vs=points;reps=[[i] for i in keep]
 else:
  ids={}
  for i,v in enumerate(points):ids.setdefault(v,i)
  vs0=list(ids)
  SCALE=max(abs(x) for v in vs0 for x in v)
  arr0=np.array(vs0,dtype=float)/SCALE
  hull=ConvexHull(arr0)
  keep=[ids[vs0[int(i)]] for i in hull.vertices]
  vs=[points[i] for i in keep]
  rev={int(j):i for i,j in enumerate(hull.vertices)}
  faces=[tuple(rev[int(j)] for j in tri) for tri in hull.simplices]
  arr=np.array(vs,dtype=float)/SCALE
  mapping={v:i for i,v in enumerate(vs)}
  reps=[]
  for p in points:
   if p in mapping:reps.append([mapping[p]])
   elif p==(0,0,0):reps.append([])
   else:reps.append(certify_removed(p,vs,faces,arr))
 assert {tuple(-x for x in v) for v in vs}==set(vs)
 stages.append(dict(m=m,keep=keep,representations=reps))
 prev=vs;hulls.append(vs)
 if m%20==0:print('hull',m,len(vs),flush=True)
(D/'finite_certificate.json').write_text(json.dumps({'initial':list(base),'stages':stages},separators=(',',':')))

rows=[]
for m in range(3,403):
 n=m-2;h=hulls[n]
 h0=max(abs(v[0]) for v in h);h1=max(abs(v[1]) for v in h)
 assert h0!=h1,(m,h0,h1)
 coord=0 if h0>h1 else 1;val=max(h0,h1)
 u=(1,0,0) if coord==0 else (0,1,0)
 word=''
 for j in range(n,0,-1):
  next_rows=[rowmul(u,T) for T in (U,V)]
  hs=[max(abs(dot(v,uu)) for v in hulls[j-1]) for uu in next_rows]
  good=[i for i,a in enumerate(hs) if a==val]
  assert len(good)==1 and max(hs)==val,(m,j,hs,val)
  choice=good[0];u=next_rows[choice];word+=str(1-choice)
 assert abs(dot(u,base))==val
 k=1
 for l,ch in enumerate(reversed(word),1):
  if ch=='1':k=2**(l+1)-k
 shift=k if coord==0 else 2**m-k
 ell=(2**(m+1)+(-1)**m)//3
 rows.append(dict(m=m,value=val,shift=shift,ell=ell,delta=shift-ell,correlation=dot(u,base),vertices=len(h),word=word,coordinate=coord))
 if m%40==0:print('unique',m,'delta',shift-ell,flush=True)
(D/'certified_maxima.json').write_text(json.dumps(rows,indent=2))
print('EXCEPTIONS',[(r['m'],r['delta']) for r in rows if r['delta']])
print('finite certificate bytes',(D/'finite_certificate.json').stat().st_size)
