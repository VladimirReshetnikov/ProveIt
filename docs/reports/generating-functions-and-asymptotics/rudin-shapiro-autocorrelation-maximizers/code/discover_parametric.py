"""Discovery: generate rational polynomial containment certificates."""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json
import numpy as np
from scipy.spatial import ConvexHull

DATA=Path(__file__).resolve().parents[1]/'data'
raw=json.loads((DATA/'template_matrices.json').read_text())
L=[[[F(x) for x in row] for row in a] for a in raw['L']]
U=[[F(x) for x in row] for row in [[1,0,2],[-1,0,2],[0,1,0]]]
V=[[F(x) for x in row] for row in [[0,1,0],[0,-1,0],[1,0,0]]]

def mm(a,b):return [[sum(a[i][k]*b[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
def scale(a,t):return [[t*x for x in row] for row in a]
def mv(a,v):return [sum(x*y for x,y in zip(row,v)) for row in a]
def pa(a,b,sg=1):
 d=a.copy()
 for t,x in b.items():d[t]=d.get(t,F(0))+sg*x
 return {t:x for t,x in d.items() if x}
def pm(a,b):
 d={}
 for (i,j),x in a.items():
  for (k,l),y in b.items():d[(i+k,j+l)]=d.get((i+k,j+l),F(0))+x*y
 return {t:x for t,x in d.items() if x}
def pvec(a):return [{(1,0):row[0],(0,0):row[1],(0,1):row[2]} for row in a]
def det(a,b,c):
 a,b,c=map(pvec,(a,b,c));out={}
 for i,j,k,sg in [(0,1,2,1),(1,2,0,1),(2,0,1,1),(0,2,1,-1),(2,1,0,-1),(1,0,2,-1)]:
  out=pa(out,pm(pm(a[i],b[j]),c[k]),sg)
 return out

def peval(p,x,z):return sum(v*x**i*z**j for (i,j),v in p.items())
def imul(a,b):
 xs=[a[0]*b[0],a[0]*b[1],a[1]*b[0],a[1]*b[1]];return min(xs),max(xs)
def ipow(a,n):
 out=(F(1),F(1))
 for _ in range(n):out=imul(out,a)
 return out

def bound(p,box):
 lo=hi=F(0)
 for (i,j),v in p.items():
  a=imul(ipow(box[0],i),ipow(box[1],j));a=imul(a,(v,v));lo+=a[0];hi+=a[1]
 return lo,hi

# Fixed rational center and generous projective box, not floating evidence.
y=[F(1),F(-1),F(1)]
for n in range(400): y=mv(U,y)
x0=F(round(y[0]/y[1]*10**12),10**12)
z0=F(round(y[2]/y[1]*10**12),10**12)
radius=F(1,10**7)
box=[(x0-radius,x0+radius),(z0-radius,z0+radius)]
center=[x0,F(1),z0]
print('CENTER',x0,z0,'radius',radius,flush=True)
# target vertices +- L_j U z
B=[scale(mm(l,U),sg) for l in L for sg in (1,-1)]
points=np.array([mv(b,center) for b in B],dtype=float)
hull=ConvexHull(points)
triples=list(tuple(map(int,t)) for t in hull.simplices)
cert=[]
for ti,T in enumerate((U,V)):
 for i,l in enumerate(L):
  q=mm(T,l)
  ids=[j for j,b in enumerate(B) if q==b]
  if ids:
   cert.append(dict(T=ti,i=i,identity=ids[0]));continue
  qf=np.array(mv(q,center),float)
  candidates=[]
  for t in triples:
   a=np.array([points[j] for j in t]).T
   weights=np.linalg.solve(a,qf)
   scores=list(weights)+[1-sum(weights)]
   if min(scores)>-1e-10:candidates.append((min(scores),t))
  candidates.sort(reverse=True)
  success=False
  for _,t in candidates:
   a,b,c=[B[j] for j in t]
   d=det(a,b,c)
   sg=1 if peval(d,x0,z0)>0 else -1
   nums=[det(q,b,c),det(a,q,c),det(a,b,q)]
   nums.append(pa(pa(pa(d,nums[0],-1),nums[1],-1),nums[2],-1))
   polys=[{e:v*sg for e,v in p.items()} for p in [d]+nums]
   bounds=[bound(p,box) for p in polys]
   if bounds[0][0]>0 and all(bd[0]>=0 for bd in bounds[1:]):
    cert.append(dict(T=ti,i=i,tetra=list(t),orientation=sg,lower_bounds=[str(bd[0]) for bd in bounds]));success=True
    print('CERT',ti,i,t, [float(bd[0]) for bd in bounds],flush=True);break
  if not success:
   print('FAILED',ti,i,'possible',len(candidates),flush=True)
   if candidates:
    t=candidates[0][1];a,b,c=[B[j] for j in t];d=det(a,b,c);sg=1 if peval(d,x0,z0)>0 else -1
    nums=[det(q,b,c),det(a,q,c),det(a,b,q)];nums.append(pa(pa(pa(d,nums[0],-1),nums[1],-1),nums[2],-1))
    print('center', [float(peval(p,x0,z0))*sg for p in [d]+nums])
    print('lower', [float(bound({e:v*sg for e,v in p.items()},box)[0]) for p in [d]+nums])
   raise RuntimeError('no tetrahedral certificate')

# strict coordinate extremality for P(z), y of identity vertex is 1.
mins=[]
for i,l in enumerate(L):
 for row in (0,1):
  if i==0 and row==1:continue
  p=pvec(l)[row]
  for sg in (1,-1):
   margin=pa({(0,0):F(1)},p,sg)
   low=bound(margin,box)[0]
   assert low>0,(i,row,sg,low)
   mins.append((low,i,row,sg))
print('coordinate gap',min(mins),flush=True)
out=dict(center=[str(x0),str(z0)],radius=str(radius),box=[[str(v) for v in b] for b in box],transitions=cert,minimum_coordinate_margin=str(min(mins)[0]))
(DATA/'polytope_certificate.json').write_text(json.dumps(out,indent=2))
