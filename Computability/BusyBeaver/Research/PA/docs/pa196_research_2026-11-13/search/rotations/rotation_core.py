#!/usr/bin/env python3
"""Bounded source-tree reassociation screen; see README.md."""
from pathlib import Path
from functools import lru_cache
from collections import Counter
import hashlib,re,time,json
p=Path(__file__).resolve().parents[2] / 'data/Program.lean'
raw=p.read_bytes()
if hashlib.sha256(raw).hexdigest()!='8c7c6c6884ecbb8f56e893404bb81162db15ef3dd6fd3212881a93994d63d872':
 raise ValueError('PA196 source hash differs from the pinned program')
s=raw.decode('utf-8')
store=[];intern={}
def interned(t):
 if t not in intern:intern[t]=len(store);store.append(t)
 return intern[t]
def node(a,b):return interned(('node',a,b))
def isnode(t):return store[t][0]=='node'
pattern=re.compile(r'\s*(\.leaf \(\.(?:inc|dec|breakTo|continueTo) \d+\)|\.leaf \(\.halt\)|[A-Za-z]\w*)');env={}
def atom(t):
 if t.startswith('.leaf'):
  m=re.fullmatch(r'\.leaf \(\.(\w+)(?: (\d+))?\)',t);return interned((m.group(1),int(m.group(2)) if m.group(2) else 0))
 return env[t]
for name,line in re.findall(r'^def (\w+) : Tree := \.node (.+)$',s,re.M):
 parts=pattern.findall(line)
 if len(parts)!=2:raise ValueError((name,line,parts))
 env[name]=node(atom(parts[0]),atom(parts[1]))
trie=re.findall(r'^def trie : Tree := (\w+)\s*$',s,re.M)
if trie!=['node172'] or trie[0] not in env:
 raise ValueError(f'unexpected source trie root: {trie}')
root=env[trie[0]]
@lru_cache(None)
def bound(t):
 a=store[t]
 if not isnode(t):return {'dec':(1,0),'breakTo':(a[1],0),'continueTo':(0,a[1])}.get(a[0],(0,0))
 x,y=bound(a[1]),bound(a[2]);return max(max(x[0]-1,0),y[0]),max(x[1],max(y[1]-1,0))
def unique(t):
 seen=set();stack=[t]
 while stack:
  x=stack.pop()
  if x in seen:continue
  seen.add(x)
  if isnode(x):stack.extend(store[x][1:])
 return seen
def metric(t):return sum(isnode(x) for x in unique(t))
def rewrite(t,old,new):
 @lru_cache(None)
 def f(x):
  if x==old:return new
  if not isnode(x):return x
  _,a,b=store[x];return node(f(a),f(b))
 return f(t)
def transforms(t):
 _,a,b=store[t]
 if isnode(a):
  _,aa,ab=store[a]
  if bound(aa)[0]==0 and bound(b)[1]==0:yield ('right',node(aa,node(ab,b)))
 if isnode(b):
  _,ba,bb=store[b]
  if bound(a)[0]==0 and bound(bb)[1]==0:yield ('left',node(node(a,ba),bb))
def allrot(root):
 for t in sorted(unique(root)):
  if isnode(t):
   for direction,new in transforms(t):yield rewrite(root,t,new),(t,direction,new)
if metric(root)!=159:raise ValueError('unexpected number of source DAG nodes')

def leaf_occurrences(t, path=()):
 if isnode(t):
  yield from leaf_occurrences(store[t][1],path+(0,))
  yield from leaf_occurrences(store[t][2],path+(1,))
 else:yield path,t

def node_occurrences(t,path=()):
 if isnode(t):
  yield path,t
  yield from node_occurrences(store[t][1],path+(0,))
  yield from node_occurrences(store[t][2],path+(1,))

def rewrite_occurrence(t,path,replacement):
 if not path:return replacement
 _,a,b=store[t]
 return node(rewrite_occurrence(a,path[1:],replacement),b) if path[0]==0 else node(a,rewrite_occurrence(b,path[1:],replacement))

def graph(root):
 leaves=list(leaf_occurrences(root)); indexes={p:i for i,(p,_) in enumerate(leaves)}
 def locate(prefix):
  cur=root; depth=0
  while depth<len(prefix) and isnode(cur):
   cur=store[cur][1+prefix[depth]];depth+=1
  if not isnode(cur):
   if any(prefix[depth:]):raise ValueError('stray one after leaf')
   return indexes[prefix[:depth]]
  while isnode(cur):
   cur=store[cur][1];prefix=prefix+(0,)
  return indexes[prefix]
 def cut(path,bit,k):
  if k==0:return path
  hits=[i for i,v in enumerate(path) if v==bit]
  if len(hits)<k:raise ValueError('insufficient control depth')
  return path[:hits[-k]]
 def after(path):
  if not path or all(path):return None
  j=len(path)-1
  while path[j]:j-=1
  return locate(path[:j]+(1,)+(0,)*(len(path)-j-1))
 result=[]
 for path,leaf in leaves:
  op,arg=store[leaf]
  if op=='inc':result.append(('inc',arg,after(path)))
  elif op=='dec':result.append(('dec',arg,after(cut(path,0,1)),after(path)))
  elif op=='breakTo':result.append(('jump',after(cut(path,0,arg))))
  elif op=='continueTo':result.append(('jump',locate(cut(path,1,arg))))
  elif op=='halt':result.append(('halt',))
  else:raise ValueError(op)
 return result

if __name__=='__main__':
 import argparse
 ap=argparse.ArgumentParser(description='Bounded PA196 source reassociation screen')
 ap.add_argument('--output',type=Path)
 ap.add_argument('--verify-graphs',action='store_true',help='compare full ordinal control graphs for each shared single rotation')
 ap.add_argument('--third-return-to-baseline',action='store_true',help='also screen third rotations from new two-step variants with 159 nodes')
 args=ap.parse_args(); start=time.monotonic()
 occurrences=Counter();occ_costs=Counter()
 for path,t in node_occurrences(root):
  for direction,new in transforms(t):
   occurrences[direction]+=1
   occ_costs[metric(rewrite_occurrence(root,path,new))]+=1
 first={};counts=Counter(); graph_checked=0
 baseline_graph=graph(root) if args.verify_graphs else None
 if baseline_graph is not None:
  if len(baseline_graph)!=3812:raise ValueError('unexpected number of source sites')
  # Deliberately violate the closure condition at the root: this must alter
  # the original last jump, guarding the independent graph comparison.
  _,left,right=store[root]
  if not isnode(left):raise ValueError('invalid-control test lost its left child')
  _,a,b=store[left]
  if bound(a)[0]==0 and bound(right)[1]==0:
   raise ValueError('invalid-control rotation unexpectedly satisfies closure')
  unsafe=graph(node(a,node(b,right)))
  if baseline_graph[3811]!=('jump',0) or unsafe[3811]!=('jump',11):
   raise ValueError('invalid-control rotation failed to alter its known jump')
 for x,desc in allrot(root):
  cost=metric(x);counts[cost]+=1
  if args.verify_graphs:
   if graph(x)!=baseline_graph:raise ValueError(f'ordinal graph mismatch after {desc}')
   graph_checked+=1
  if cost<=160:first.setdefault(x,desc)
 found=[];second=0;second_base={}
 for x,d1 in first.items():
  for y,d2 in allrot(x):
   second+=1;cost=metric(y)
   if cost<159:
    if args.verify_graphs and graph(y)!=baseline_graph:raise ValueError('two-step ordinal graph mismatch')
    found.append({'nodes':cost,'first':d1,'second':d2})
   if args.third_return_to_baseline and cost==159 and y!=root and y not in first:
    second_base.setdefault(y,(d1,d2))
 third=0;third_found=[]
 if args.third_return_to_baseline:
  for y,(d1,d2) in second_base.items():
   for z,d3 in allrot(y):
    third+=1;cost=metric(z)
    if cost<159:
     if args.verify_graphs and graph(z)!=baseline_graph:raise ValueError('three-step ordinal graph mismatch')
     third_found.append({'nodes':cost,'first':d1,'second':d2,'third':d3})
 result={'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
         'leaves':len(list(leaf_occurrences(root))),'baseline_unique_internal_nodes':159,
         'single_occurrence_direction_counts':dict(occurrences),'single_occurrence_cost_counts':dict(occ_costs),
         'global_single_cost_counts':dict(counts),'unique_first_with_at_most_160_nodes':len(first),
         'two_global_rotation_pairs':second,'two_step_improvements':found,
         'single_global_full_graphs_checked':graph_checked,'elapsed_seconds':round(time.monotonic()-start,3)}
 if args.third_return_to_baseline:
  result.update({'third_return_intermediates':len(second_base),'third_global_rotation_pairs':third,
                 'three_step_improvements':third_found})
 result['elapsed_seconds']=round(time.monotonic()-start,3)
 out=json.dumps(result,indent=2,sort_keys=True)+'\n';print(out,end='')
 if args.output:args.output.write_text(out)
