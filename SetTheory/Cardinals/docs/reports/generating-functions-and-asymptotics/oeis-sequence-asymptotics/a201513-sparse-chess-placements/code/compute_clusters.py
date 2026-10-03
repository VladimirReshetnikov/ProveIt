#!/usr/bin/env python3
"""Exact connected-support cluster coefficients for finite-range chess moves.
No fitted or floating-point coefficients. Python standard library only.
"""
from functools import lru_cache
from fractions import Fraction as F
import json,math,argparse

MOVES={
 'king':[(x,y) for x in (-1,0,1) for y in (-1,0,1) if (x,y)!=(0,0)],
 'knight':[(x,y) for x,y in [(1,2),(2,1),(-1,2),(-2,1),(1,-2),(2,-1),(-1,-2),(-2,-1)]],
 'wazir':[(1,0),(-1,0),(0,1),(0,-1)],
 'fers':[(1,1),(-1,1),(1,-1),(-1,-1)]}

def normalize(S):
 x=min(p[0] for p in S);y=min(p[1] for p in S)
 return tuple(sorted((a-x,b-y) for a,b in S))

def supports(moves,J):
 layer={((0,0),)}
 for m in range(1,J+1):
  yield layer
  nxt=set()
  for S in layer:
   ss=set(S)
   for x,y in S:
    for dx,dy in moves:
     v=(x+dx,y+dy)
     if v not in ss:nxt.add(normalize(ss|{v}))
  layer=nxt

def adjacency(S,moves):
 M=set(moves);return tuple(sum(1<<j for j,q in enumerate(S) if j!=i and (q[0]-p[0],q[1]-p[1]) in M) for i,p in enumerate(S))

@lru_cache(None)
def cluster_weight(adj,J):
 """Return (j times weight_j(S)) for j=0..J, via exact support Mobius inversion."""
 m=len(adj); totals=[0]*(J+1)
 for T in range(1,1<<m):
  counts=[0]*(J+1)
  U=T
  while True:
   if all(not(adj[i]&U) for i in range(m) if (U>>i)&1):counts[U.bit_count()]+=1
   if U==0:break
   U=(U-1)&T
  logs=[0]*(J+1)
  for j in range(1,J+1):
   logs[j]=j*counts[j]-sum(logs[k]*counts[j-k] for k in range(1,j))
  sign=(-1)**(m-T.bit_count())
  for j in range(1,J+1):totals[j]+=sign*logs[j]
 return tuple(totals)

def clusters(piece,J):
 ans=[[F(0),F(0),F(0)] for j in range(J+1)]
 stats=[]
 for layer in supports(MOVES[piece],J):
  stats.append(len(layer))
  for S in layer:
   w=max(x for x,y in S);h=max(y for x,y in S)
   weights=cluster_weight(adjacency(S,MOVES[piece]),J)
   for j in range(len(S),J+1):
    b=F(weights[j],j)
    ans[j][0]+=b;ans[j][1]-=b*(w+h);ans[j][2]+=b*w*h
 return ans,stats

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--order',type=int,default=5);p.add_argument('--pieces',nargs='+',default=['king','knight','wazir','fers']);a=p.parse_args()
 out={}
 for piece in a.pieces:
  b,stats=clusters(piece,a.order)
  out[piece]={'support_counts':stats,'b_j_coefficients_n2_n_1':[[str(x) for x in row] for row in b]}
  print(piece,out[piece],flush=True)
 with open('cluster_coefficients.json','w') as f:json.dump(out,f,indent=2)
