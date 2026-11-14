#!/usr/bin/env python3
"""Bounded source-tree reassociation screen; see README.md."""
from pathlib import Path
from functools import lru_cache
from collections import Counter
import hashlib,re,time,json
p=Path(__file__).resolve().parent / 'inputs/Program.lean'
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

