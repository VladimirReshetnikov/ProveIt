"""Discover an exact six-step rational projective trapping certificate."""
from fractions import Fraction as F
from pathlib import Path
import json
D=Path(__file__).resolve().parents[1]/'data'
a=json.loads((D/'polytope_certificate.json').read_text())
center=[F(t) for t in a['center']]
S=[tuple(map(F,b)) for b in a['box']]
R=[(c-F(1,10**9),c+F(1,10**9)) for c in center]
U=[[1,0,2],[-1,0,2],[0,1,0]]
M=[[-x for x in row] for row in U]
I=[[1,0,0],[0,1,0],[0,0,1]]
def mm(a,b):return [[sum(a[i][k]*b[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
def linbound(row,box):
 lo=hi=F(row[1])
 for a,(l,h) in zip((row[0],row[2]),box):
  lo+=min(a*l,a*h);hi+=max(a*l,a*h)
 return lo,hi
def maps_into(M,source,target):
 low=linbound(M[1],source)[0]
 if low<=0:return False,low
 margins=[low]
 for i,(l,h) in zip((0,2),target):
  margins.append(linbound([M[i][j]-l*M[1][j] for j in range(3)],source)[0])
  margins.append(linbound([h*M[1][j]-M[i][j] for j in range(3)],source)[0])
 return min(margins)>0,min(margins)
P=I
for q in range(1,65):
 P=mm(M,P)
 ok,v=maps_into(P,R,R)
 print(q,ok,float(v))
 if ok:
  good=True;Q=I
  for j in range(q):
   yes,margin=maps_into(Q,R,S)
   if not yes: print('intermediate fail',j,margin);good=False;break
   Q=mm(M,Q)
  if good:break
else:raise ValueError('not found')
v=[1,-1,1]
for n in range(400):v=[sum(a*b for a,b in zip(row,v)) for row in U]
ratios=[F(v[0],v[1]),F(v[2],v[1])]
assert all(l<=x<=h for x,(l,h) in zip(ratios,R))
a['inner_box']=[[str(v) for v in b] for b in R]
a['block_length']=q
a['entry_level']=402
a['entry_word_length']=400
(D/'polytope_certificate.json').write_text(json.dumps(a,indent=2))
print('SUCCESS',q,'R',R,'relative', [float(x-c) for x,c in zip(ratios,center)])
