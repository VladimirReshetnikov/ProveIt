"""Build the fixed weight-five, level-four imaginary double-shuffle audit.

The exported witness proves non-membership in this particular homogeneous
row space. It neither proves nor disproves the numerical S4 period identity.
The formal endpoint T is used only in shuffle-minus-stuffle differences
whose divergent coordinate cancels. Rows retain a documented generator
order, including zero or duplicate rows, for reproducibility.
"""
import sympy as s
from math import comb
from collections import defaultdict
from fractions import Fraction as F
w=5

def can(a,b,x,y):
 x%=4;y%=4
 if x%2==0 and y%2==0:return None,0
 cp=((-x)%4,(-y)%4)
 if (x,y)<=cp:return (a,b,x,y),1
 return (a,b,*cp),-1
keys=sorted({can(a,w-a,x,y)[0] for a in range(1,w) for x in range(4) for y in range(4) if (a,x)!=(1,0)}-{None})
idx={k:i for i,k in enumerate(keys)}
pi,L,G,B4,Z3,T=s.symbols('pi L G B4 Z3 T',real=True)
def li(n,x):
 x%=4
 if x==0:
  return {1:T,2:pi**2/6,3:Z3,4:pi**4/90,5:s.zeta(5)}[n]
 if x==2:
  if n==1:return -L
  return -(1-s.Rational(1,2)**(n-1))*li(n,0)
 if n==1:return -L/2+ (1 if x==1 else -1)*s.I*pi/4
 be={2:G,3:pi**3/32,4:B4,5:5*pi**5/1536}[n]
 return -(s.Rational(1,2)**n)*(1-s.Rational(1,2)**(n-1))*li(n,0)+(1 if x==1 else -1)*s.I*be

def add(d,a,b,x,y,c):
 k,sg=can(a,b,x,y)
 if sg:d[k]+=c*sg

def stuff(p,q,x,y):
 d=defaultdict(int);add(d,p,q,x,y,1);add(d,q,p,y,x,1)
 return d,s.expand(s.im(li(p,x)*li(q,y)-li(w,x+y)))
def shuf(p,q,x,y):
 d=defaultdict(int)
 for k in range(p):add(d,q+k,p-k,y,x-y,comb(q-1+k,k))
 for k in range(q):add(d,p+k,q-k,x,y-x,comb(p-1+k,k))
 return d,s.expand(s.im(li(p,x)*li(q,y)))
rows=[];rhs=[];labels=[]
def row(d,r,label):
 d={k:v for k,v in d.items() if v}
 if any(k not in idx for k in d): print('divergent',label,d);return
 rows.append([d.get(k,0) for k in keys]);rhs.append(r);labels.append(label)
for p in range(1,w):
 q=w-p
 for x in range(4):
  for y in range(4):
   ds,rs=stuff(p,q,x,y);dh,rh=shuf(p,q,x,y)
   if (p,x)!=(1,0) and (q,y)!=(1,0):
    row(ds,rs,('stuffle',p,q,x,y));row(dh,rh,('shuffle',p,q,x,y))
   else:
    d=defaultdict(int,dh)
    for k,v in ds.items():d[k]-=v
    row(d,rh-rs,('regds',p,q,x,y))
# Distribution: sum signs Li_ab(x,y)=2^(2-w) Li_ab(x2,y2)
for a in range(1,w):
 b=w-a
 for x in range(2):
  for y in range(2):
   d=defaultdict(int)
   for e in (0,2):
    for f in (0,2):add(d,a,b,x+e,y+f,1)
   add(d,a,b,2*x,2*y,-s.Rational(2)**(2-w))
   if (a!=1 or x==1):row(d,0,('distribution',a,b,x,y))
A=s.Matrix(rows);r=s.Matrix(rhs)
print('shape',A.shape,'rank',A.rank())
# 7S4 =4g41-3g32-9g23+ pi5/32 -27GZ3/32 -14B4L
# S4=g41+B41 => 3g41+3g32+9g23+7B41 = pi5/32 -27GZ3/32 -14B4L
v=defaultdict(int)
for a,b,x,y,c in [(4,1,1,0,3),(3,2,1,0,3),(2,3,1,0,9),(4,1,1,2,7)]:add(v,a,b,x,y,c)
tar=s.Matrix([v.get(k,0) for k in keys])
try:
 sol,par=A.T.gauss_jordan_solve(tar)
 sol=sol.subs({v:0 for v in par})
 expr=s.expand((sol.T*r)[0]);print('PROVED',expr)
 for i,x in enumerate(sol):
  if x:print(x,labels[i])
except ValueError:
 print('NOT IN ROWSPACE',A.col_join(tar.T).rank())
 null=A.nullspace();print('obstructions',[(i,(tar.T*n)[0]) for i,n in enumerate(null) if (tar.T*n)[0]!=0])

# A dual certificate concerns this finite formal law system, not true periods.
import json
from pathlib import Path
root=Path(__file__).resolve().parents[1]
n=next(n for n in A.nullspace() if (tar.T*n)[0]!=0)
den=s.ilcm(*[x.q for x in n]);n=n*den
assert A*n==s.zeros(A.rows,1)
assert (tar.T*n)[0]!=0
report={'scope':'Homogeneous left-hand sides of the 134 explicitly listed weight-five imaginary level-four rows only.',
 'status':'Target is outside this formal row space; this does not disprove S4.',
 'columns':[list(k) for k in keys], 'rows':[list(map(int,row)) for row in rows],
 'row_labels':[list(x) for x in labels], 'rank':int(A.rank()),
 'augmented_rank':int(A.col_join(tar.T).rank()),
 'target':list(map(int,tar)), 'dual_witness':list(map(int,n)),
 'witness_pairing':int((tar.T*n)[0])}
(root/'certificates'/'s4_rowspace_obstruction.json').write_text(json.dumps(report,indent=2)+'\n')
print('DUAL WITNESS', [(k,int(n[i])) for i,k in enumerate(keys) if n[i]], 'pairing', (tar.T*n)[0])
