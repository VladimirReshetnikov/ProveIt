#!/usr/bin/env python3
"""Discover exact affine summaries of closed total source fragments.
Transfer recognition and disjointness witnesses; discovery, not binary proof.
"""
from pathlib import Path
import sys,json,functools,collections
ROOT=Path(__file__).resolve().parents[1]
from source_decoder import Decoder,read_json
nodes,root,_=read_json(ROOT/'experiments/source_inputs/original203.json')
D=Decoder(nodes,root)
N=10
identity=tuple(tuple(int(i==j) for j in range(N)) for i in range(N))

def compose(A,B): # B after A
 return tuple(tuple(sum(B[i][k]*A[k][j] for k in range(N)) for j in range(N)) for i in range(N))

def incr(reg):
 M=[list(row) for row in identity];M[reg][9]+=1
 return tuple(tuple(row) for row in M)

def linear_loop(n):
 if D.bounds(('N',n))!=(0,0):return None
 extended=dict(nodes);q=max(extended)+1;extended[q]=(('N',n),('H',))
 dec=Decoder(extended,q);g=dec.graph();start=dec.leaf('')
 ds=[i for i,(e,_) in enumerate(g) if e[0]=='D']
 if len(ds)!=1:return None
 di=ds[0];r=g[di][0][1]
 def chain(i):
  seen=set();incs=[0]*9
  while g[i][0][0] not in ('D','H'):
   if i in seen:return None
   seen.add(i);e,nxt=g[i]
   if e[0]=='I':incs[e[1]]+=1
   else:assert e[0] in ('B','C')
   i=nxt[0]
  return i,incs
 prefix=chain(start);cycle=chain(g[di][1][0]);suffix=chain(g[di][1][1])
 if any(x is None for x in (prefix,cycle,suffix)):return None
 if prefix[0]!=di or cycle[0]!=di or g[suffix[0]][0][0]!='H' or cycle[1][r]:return None
 M=[list(row) for row in identity]
 # counter initial x_r + prefix_r; loop adds count * cycle vector; consumes all of r
 for k in range(9):
  if k==r:M[k]=[0]*10;M[k][9]=suffix[1][k]
  else:M[k][r]+=cycle[1][k];M[k][9]+=prefix[1][k]+prefix[1][r]*cycle[1][k]+suffix[1][k]
 return tuple(tuple(row) for row in M),{'kind':'single_transfer_loop','counter':r,'prefix':prefix[1],'per_iteration':cycle[1],'suffix':suffix[1]}

proof={}
@functools.cache
def summary(e):
 if e[0]=='I':return incr(e[1])
 if e[0]!='N':return None
 a,b=nodes[e[1]]
 A,B=summary(a),summary(b)
 if A is not None and B is not None and D.bounds(a)==D.bounds(b)==(0,0):
  proof[e[1]]={'kind':'composition','left':a,'right':b};return compose(A,B)
 ans=linear_loop(e[1])
 if ans:proof[e[1]]=ans[1];return ans[0]
 return None
for n in nodes:summary(('N',n))
groups=collections.defaultdict(list)
for n in nodes:
 M=summary(('N',n))
 if M is not None:groups[M].append(n)
res={'nodes':len(nodes),'total_affine_nodes':sum(len(v) for v in groups.values()),'distinct_maps':len(groups),'equivalent_node_groups':[v for v in groups.values() if len(v)>1],'proofs':proof,'maps':{str(n):summary(('N',n)) for n in proof}}
(Path.cwd()/'total_fragment_summaries.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps({k:v for k,v in res.items() if k not in ('proofs','maps')},indent=2))
for group in res['equivalent_node_groups']:
 print('EQUIVALENT',group)
 for n in group:print(n,nodes[n],proof[n])
