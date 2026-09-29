"""Exploratory finite-prefix strengthening of the Bui polyomino system."""
from fractions import Fraction as Q
from pathlib import Path
import json, sys, time
import numpy as np
from scipy.optimize import root
NAMES='c d e f g h p q r s t u v w x y z'.split()
SINGLE=[(0,0)]; PAIR=[(0,0),(1,0)]; TRIPLE=[(0,0),(1,0),(2,0)]
BELOW=[(-1,-1),(0,-1),(1,-1)]; BELOW4=BELOW+[(2,-1)]
PATTERNS=[
(SINGLE,[(-1,1),(1,1),(-1,0),(1,0)]+BELOW),
(SINGLE,[(-1,1),(-1,0),(1,0)]+BELOW),
(SINGLE,[(-1,0),(1,0)]+BELOW),
(SINGLE,BELOW),
(SINGLE,[(-1,0)]+BELOW),
(SINGLE,[(-1,1),(-1,0)]+BELOW),
(PAIR,[(0,-1),(1,-1),(2,-1)]),
(PAIR,[(-1,0)]+BELOW),
(PAIR,[(-1,1),(-1,0)]+BELOW4),
(PAIR,[(-1,1),(-1,0)]+BELOW),
(PAIR,[(-1,0)]+BELOW4),
(PAIR,BELOW4),
(TRIPLE,[(-1,0)]+BELOW4),
(TRIPLE,[(-1,1),(-1,0)]+BELOW4),
(PAIR,[(-1,0),(2,0)]+BELOW4),
(PAIR,[(-1,1),(-1,0),(2,0)]+BELOW4),
(PAIR,[(-1,1),(2,1),(-1,0),(2,0)]+BELOW4),
]
# Each monomial is (power of t, tuple of variable indices). Coefficient = 1.
# This provides an independently inspectable representation of the map.
TERMS=[[(1,()),(1,(2,))],[(1,()),(1,(4,))],[(1,()),(1,(3,))],
[(0,(4,)),(0,(6,))],[(0,(2,)),(0,(7,))],[(0,(1,)),(0,(9,))],
[(0,(2,5)),(0,(7,1)),(0,(14,8)),(0,(12,15)),(0,(11,15,16))],
[(1,(4,)),(1,(4,2)),(2,(11,)),(2,(10,4)),(2,(8,11))],
[(0,(15,)),(0,(13,))],
[(1,(4,)),(1,(2,2)),(2,(10,)),(2,(14,4)),(2,(15,11))],
[(0,(14,)),(0,(12,))],
[(0,(1,5)),(0,(9,1)),(0,(15,8)),(0,(13,15)),(0,(11,16,16))],
[(1,(9,)),(2,(4,4)),(2,(10,2)),(2,(8,10))],
[(1,(9,)),(2,(2,4)),(2,(14,2)),(2,(15,10))],
[(1,(1,)),(2,(4,)),(2,(11,))],
[(1,(0,)),(2,(4,)),(2,(10,))],
[(1,(0,)),(2,(2,)),(2,(14,))]]

def fmap(t,a):
 out=[]
 for row in TERMS:
  s=0
  for k,inds in row:
   v=t**k
   for j in inds:v*=a[j]
   s+=v
  out.append(s)
 return out

def jac(t,a):
 out=np.zeros((17,17))
 for i,row in enumerate(TERMS):
  for k,inds in row:
   for l,j in enumerate(inds):
    v=t**k
    for h,q in enumerate(inds):
     if h!=l:v*=a[q]
    out[i,j]+=v
 return out

def conv(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  if x:
   for j,y in enumerate(b):
    if y:c[i+j]+=x*y
 return c

def polyf(P):
 out=[]
 for row in TERMS:
  s=[0]
  for k,inds in row:
   v=[0]*k+[1]
   for j in inds:v=conv(v,P[j])
   if len(s)<len(v):s += [0]*(len(v)-len(s))
   for j,w in enumerate(v):s[j]+=w
  out.append(s)
 return out

def evalpoly(p,t):
 v=0
 for a in reversed(p):v=v*t+a
 return v

def defects(counts,N):
 P=[row[:N+1] for row in counts]; F=polyf(P)
 D=[[F[i][j]-P[i][j] for j in range(N+1)] for i in range(17)]
 assert all(v>=0 for row in D for v in row)
 return P,D

# Fixed polyominoes: translation only, not rotation or reflection.
def enumerate_counts(N):
 counts=[[0] for _ in NAMES]; sizes=[0]; shapes={((0,0),)}
 for n in range(1,N+1):
  tick=time.time(); total=[0]*17
  for shape in shapes:
   s=set(shape)
   for x,y in shape:
    for i,(req,ban) in enumerate(PATTERNS):
     if all((x+dx,y+dy) in s for dx,dy in req[1:]) and not any((x+dx,y+dy) in s for dx,dy in ban):total[i]+=1
  sizes.append(len(shapes))
  for row,v in zip(counts,total):row.append(v)
  print(n,len(shapes),total,'sec',round(time.time()-tick,2),flush=True)
  if n<N:
   next_shapes=set()
   for shape in shapes:
    s=set(shape)
    boundary={(x+dx,y+dy) for x,y in s for dx,dy in [(1,0),(-1,0),(0,1),(0,-1)]}-s
    for p in boundary:
     q=shape+(p,); mx=min(x for x,y in q); my=min(y for x,y in q)
     next_shapes.add(tuple(sorted((x-mx,y-my) for x,y in q)))
   shapes=next_shapes
 return counts,sizes

def critical(counts,N,guess=None):
 P,D=defects(counts,N)
 if guess is None:guess=np.r_[np.array([3482045,4310668,5751028,16014774,9499305,7394875,6515468,3748277,2390936,3084206,2902315,5050537,1238300,1015088,1664015,1375847,1132149])/1e7,2000/9047]
 def fun(z):
  a=z[:17];t=z[17]
  return np.r_[np.array(fmap(t,a))-a-np.array([evalpoly(d,t) for d in D]),np.linalg.det(np.eye(17)-jac(t,a))]
 sol=root(fun,guess,tol=1e-11)
 a=sol.x[:17];t=sol.x[17]
 print('critical',N,sol.success,'Lambda',1/t,'t',t,'resid',np.max(abs(fun(sol.x))),'minTail',min(a-np.array([evalpoly(p,t) for p in P])),flush=True)
 return sol.x

if __name__=='__main__':
 data=Path(__file__).resolve().parent.parent/'data'
 if len(sys.argv)>1 and sys.argv[1]=='enumerate':
  N=int(sys.argv[2])
  if not 1 <= N <= 11: raise ValueError('Reference enumeration is limited to 1..11')
  counts,sizes=enumerate_counts(N)
  output = Path(sys.argv[3]) if len(sys.argv)>3 else Path(f'profiles_reference_{N}.json')
  output.write_text(json.dumps({'names':NAMES,'counts':counts,'polyominoes':sizes},indent=2)+'\n')
  print('Wrote',output)
 else:
  d=json.loads((data/'profiles.json').read_text());guess=None;results=[]
  for N in range(1,len(d['polyominoes'])):
   guess=critical(d['counts'],N,guess);results.append(guess.tolist())
  output=Path('critical_estimates_new.json')
  output.write_text(json.dumps(results,indent=2)+'\n')
  print('Wrote',output)
