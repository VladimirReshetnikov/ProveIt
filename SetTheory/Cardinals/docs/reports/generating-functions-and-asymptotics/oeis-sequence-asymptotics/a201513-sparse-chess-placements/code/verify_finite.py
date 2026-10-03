#!/usr/bin/env python3
"""Independent finite-board checks of connected-support cluster enumeration."""
from compute_clusters import MOVES,supports,adjacency,cluster_weight
from fractions import Fraction as F

def independence_counts(n,moves,J):
 pts=[(x,y) for x in range(n) for y in range(n)]
 adj=adjacency(pts,moves);out=[0]*(J+1)
 def dfs(available,k):
  out[k]+=1
  if k==J:return
  while available:
   b=available&-available;available-=b;i=b.bit_length()-1
   dfs(available&~adj[i],k+1)
 dfs((1<<len(pts))-1,0)
 return out

def log_coeffs(a):
 out=[0]*len(a)
 for j in range(1,len(a)):out[j]=j*a[j]-sum(out[k]*a[j-k] for k in range(1,j))
 return out

def from_supports(n,moves,J):
 out=[0]*(J+1)
 for layer in supports(moves,J):
  for S in layer:
   w=max(x for x,y in S);h=max(y for x,y in S)
   trans=max(n-w,0)*max(n-h,0)
   if not trans:continue
   wgt=cluster_weight(adjacency(S,moves),J)
   for j in range(len(S),J+1):out[j]+=trans*wgt[j]
 return out

if __name__=='__main__':
 J=6
 for piece,moves in MOVES.items():
  for n in (3,4,5):
   a=independence_counts(n,moves,J)
   got=from_supports(n,moves,J);want=log_coeffs(a)
   assert got==want,(piece,n,got,want)
   print(piece,n,'independent counts=',a,'j*b_j=',got,'PASS',flush=True)
 print('All 12 independent finite-board checks pass through cluster order 6.')
