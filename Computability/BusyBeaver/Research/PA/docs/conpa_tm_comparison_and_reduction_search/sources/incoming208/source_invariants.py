#!/usr/bin/env python3
"""Finite single-register abstractions for the exact PA196 source graph."""
import collections,functools,json,sys
import compile_ax as c
g=c.g
def cfg(tree):
 leaves=g.flatten(tree);ranges={}
 for i,(p,op) in enumerate(leaves):
  for n in range(len(p)+1):
   a=p[:n]
   if a not in ranges:ranges[a]=[i,i+1]
   else:ranges[a][1]=i+1
 def jump(p,bit,k):
  for i in reversed(range(len(p))):
   if p[i]==bit:
    k-=1
    if k==0:return ranges[p[:i]][1 if bit==0 else 0]%len(leaves)
  return 0
 out=[]
 for i,(p,op) in enumerate(leaves):
  kind=op[0];arg=op[1] if len(op)>1 else 0;nxt=(i+1)%len(leaves)
  if kind=='inc':ts=[nxt]
  elif kind=='dec':ts=[jump(p,0,1),nxt]
  elif kind=='breakTo':ts=[jump(p,0,arg)]
  elif kind=='continueTo':ts=[jump(p,1,arg)]
  else:ts=[]
  out.append([kind,arg,ts])
 return leaves,out
def closure(cfg,r,seed_pc=25):
 reached=[set() for x in cfg];initial=2 if r==0 else 0;reached[seed_pc].add(initial);q=collections.deque([(seed_pc,initial)])
 def succ(i,x):
  op,arg,ts=cfg[i]
  if op=='inc':return[(ts[0],min(2,x+1) if arg==r else x)]
  if op=='dec':
   if arg!=r:return[(k,x) for k in ts]
   if x==0:return[(ts[0],0)]
   if x==1:return[(ts[1],0)]
   return[(ts[1],1),(ts[1],2)]
  return[(ts[0],x)] if ts else[]
 while q:
  i,x=q.popleft()
  for j,y in succ(i,x):
   if y not in reached[j]:reached[j].add(y);q.append((j,y))
 # Independent closure check, retained even under python -O.
 if initial not in reached[seed_pc]:raise ValueError('seed')
 for i,xs in enumerate(reached):
  for x in xs:
   if any(y not in reached[j] for j,y in succ(i,x)):raise ValueError('not inductive')
 return reached
def main():
 ns=c.macro_info()[0];leaves,G=cfg(ns['trie']);inv={};guards=[]
 for r in range(9):
  reached=closure(G,r);inv[r]=[sorted(x) for x in reached]
  for i,(op,arg,ts) in enumerate(G):
   if op=='dec' and arg==r and reached[i] and(reached[i]=={0} or 0 not in reached[i]):guards.append({'site':i,'path':leaves[i][0],'register':r,'categories':sorted(reached[i]),'targets':ts})
 out={'source_sites':len(G),'seed_pc':25,'seed_registers':[2,0,0,0,0,0,0,0,0],'seed_source':'PA196/Arithmetic/Machine/EndpointInternalStartupFrame.lean startup_refines_nat','categories':['zero','one','at_least_two'],'guards':guards,'inductive_sets':inv}
 (c.HERE/'source_category_invariants.json').write_text(json.dumps(out,indent=2))
 print('Guarded decrements',len(guards));print(*guards,sep='\n')
if __name__=='__main__':main()
