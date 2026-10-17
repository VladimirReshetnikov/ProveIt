#!/usr/bin/env python3
"""Finite abstract interpretation of the exact published register program.
Each register is a union of {0},...,{K},{K+1,K+2,...}; componentwise join
forgets correlations. The fixed-point certificate is independently checkable.
"""
from pathlib import Path
from collections import deque,Counter
import argparse,json,time
from context_search import program_sites
ROOT=Path(__file__).parent

def build(k=2):
 sites=program_sites(ROOT/'sources/Prog254.v')
 trie={}
 for i,(q,op,r) in enumerate(sites):
  node=trie
  for c in q:node=node.setdefault(c,{})
  node['leaf']=i
 def leaf(path):
  node=trie;pos=0
  while 'leaf' not in node:
   node=node[path[pos] if pos<len(path) else '0'];pos+=1
  return node['leaf']
 def inc(p):
  if '0' not in p:return ''
  j=p.rindex('0');return p[:j]+'1'
 def strip(b,n,p):
  while n>0 and p:
   if p[-1]==b:n-=1
   p=p[:-1]
  return p
 edges=[]
 for q,op,r in sites:
  if op=='CI':edges.append([(None,leaf(inc(q)))])
  elif op=='CD':edges.append([(0,leaf(inc(strip('0',1,q)))),(1,leaf(inc(q)))])
  elif op=='CC':edges.append([(None,leaf(strip('1',r,q)))])
  elif op=='CB':edges.append([(None,leaf(inc(strip('0',r,q))))])
  else:edges.append([])
 return sites,edges,leaf('')

def transfer(mask,k,op):
 out=0
 for i in range(k+2):
  if mask>>i&1:
   if op=='inc':out|=1<<min(i+1,k+1)
   elif i==k+1:out|=(1<<k)|(1<<(k+1))
   else:out|=1<<max(i-1,0)
 return out

def compute(k):
 sites,edges,initial=build(k)
 inputs=[None]*len(sites)
 init=[1]*9;init[6]=1<<min(2,k+1)
 inputs[initial]=init
 todo=deque([initial]);queued={initial};rounds=0
 while todo:
  i=todo.popleft();queued.remove(i);rounds+=1
  q,op,r=sites[i];state=inputs[i]
  for branch,dest in edges[i]:
   out=state.copy()
   if op=='CD':
    mask=out[r] & (1 if branch==0 else ~1)
    if not mask:continue
    out[r]=1 if branch==0 else transfer(mask,k,'dec')
   elif op=='CI':out[r]=transfer(out[r],k,'inc')
   if inputs[dest] is None:inputs[dest]=out;changed=True
   else:
    newer=[a|b for a,b in zip(inputs[dest],out)]
    changed=newer!=inputs[dest];inputs[dest]=newer
   if changed and dest not in queued:todo.append(dest);queued.add(dest)
 allowed=[];removed=[];unreachable=[]
 for i,(q,op,r) in enumerate(sites):
  if inputs[i] is None:unreachable.append(i)
  for branch in ('z','p') if op=='CD' else ('-',):
   feasible=inputs[i] is not None and (op!='CD' or bool(inputs[i][r] & (1 if branch=='z' else ~1)))
   (allowed if feasible else removed).append([i,branch])
 out={'k':k,'sites':len(sites),'fixed_point_iterations':rounds,'allowed_cases':len(allowed),'removed_cases':len(removed),'unreachable_sites':unreachable,'removed':removed,'inputs':inputs,'allowed':allowed}
 return out

def main():
 p=argparse.ArgumentParser();p.add_argument('--k',type=int,default=2);a=p.parse_args();t=time.monotonic();out=compute(a.k);out['elapsed']=time.monotonic()-t
 (ROOT/f'abstract_reachability_k{a.k}.json').write_text(json.dumps(out,indent=2)+'\n')
 print({k:v for k,v in out.items() if k not in ['inputs','allowed','removed','unreachable_sites']});print('unreachable',len(out['unreachable_sites']));print('removed',out['removed'][:60])
if __name__=='__main__':main()
