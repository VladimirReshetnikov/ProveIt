"""Exact sparse representation of the seventeen Bui recurrences.

All functions use integer or rational arithmetic when given such inputs.
No numerical packages are needed by the certificate verifier.
"""
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

