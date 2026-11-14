#!/usr/bin/env python3
"""Jump-retargeting source rotations. Adapted from the pinned ProveIt rotation checker; MIT notices retained. Finite source checks only; no smaller TM is claimed."""
from pathlib import Path
from functools import lru_cache
from collections import Counter
import hashlib,re,time,json
p=Path(__file__).with_name('Program.lean')
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


@lru_cache(None)
def size(t):
 if not isnode(t):return 1
 return size(store[t][1])+size(store[t][2])
@lru_cache(None)
def zr(t):
 if not isnode(t):return 0,0
 a,b=store[t][1:];x,xx=zr(a);y,yy=zr(b)
 return x+1,max(x+1,xx,yy)
def inf(t,start=0,anc=()):
 if not isnode(t):yield (t,start,anc);return
 a,b=store[t][1:];end=start+size(t)
 yield from inf(a,start,((0,start,end),)+anc)
 yield from inf(b,start+size(a),((1,start,end),)+anc)
old=graph(root)
def repair(t):
 replacements=[];edits=[]
 for leaf,i,anc in inf(t):
  op,arg=store[leaf];rec=old[i]
  if op=='dec':
   z=next((end for b,start,end in anc if b==0),None)
   if z!=rec[2]:return None,'dec'
  if op in ('continueTo','breakTo'):
   bit=1 if op=='continueTo' else 0
   destinations=[start if bit else end for b,start,end in anc if b==bit]
   try:k=destinations.index(rec[1])+1
   except ValueError:return None,'jump'
   if k>3:return None,'depth'
   if k!=arg:edits.append((i,op,arg,k))
   leaf=interned((op,k))
  replacements.append(leaf)
 cursor=0
 def f(x):
  nonlocal cursor
  if not isnode(x):
   z=replacements[cursor];cursor+=1;return z
  a,b=store[x][1:];return node(f(a),f(b))
 z=f(t)
 if graph(z)!=old:raise ValueError('repair not equal')
 return z,edits

def transforms(t):
 a,b=store[t][1:]
 if isnode(a):
  aa,ab=store[a][1:];yield 'right',node(aa,node(ab,b))
 if isnode(b):
  ba,bb=store[b][1:];yield 'left',node(node(a,ba),bb)

def encode(t):
 rs={};ids={}
 def f(x):
  if not isnode(x):return list(store[x])
  if x in ids:return ids[x]
  a,b=store[x][1:];r=[f(a),f(b)];n=f'n{len(rs)}';ids[x]=n;rs[n]=r;return n
 root=f(t);return dict(root=root,rules=rs)




def main():
 import argparse
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--second',action='store_true',help='also test second rotations after the 11 new first repairs with at most160 nodes')
 ap.add_argument('--output',type=Path,default=Path(__file__).with_name('receipt.json'))
 args=ap.parse_args();counts=Counter();fails=Counter();candidates=[];accepted=0;examined=0
 for t in sorted(unique(root)):
  if not isnode(t):continue
  for direction,r in transforms(t):
   examined+=1;z,edits=repair(rewrite(root,t,r))
   if z is None:fails[edits]+=1;continue
   accepted+=1;k=(metric(z),zr(z)[1]);counts[k]+=1
   if edits:candidates.append(dict(node=t,direction=direction,nodes=k[0],maxzero=k[1],edits=edits,grammar=encode(z)))
 result=dict(source_sha256=hashlib.sha256(raw).hexdigest(),first_examined=examined,first_accepted=accepted,first_histogram={str(k):v for k,v in sorted(counts.items())},first_rejections=dict(fails),retargeted_variants=len(candidates),scope='Exact source CFG only; no physical transition table or PA equivalence follows')
 if args.second:
  count=0;hist=Counter();bad=Counter();improvements=[];firsts=0
  for j,rec in enumerate(candidates):
   if rec['nodes']>160:continue
   firsts+=1;rules=rec['grammar']['rules']
   def decode(t):
    if isinstance(t,list):return interned(tuple(t))
    a,b=rules[t];return node(decode(a),decode(b))
   r=decode(rec['grammar']['root'])
   for t in sorted(unique(r)):
    if not isnode(t):continue
    for direction,nt in transforms(t):
     count+=1;z,edits=repair(rewrite(r,t,nt))
     if z is None:bad[edits]+=1;continue
     k=(metric(z),zr(z)[1]);hist[k]+=1
     if k[0]<159:improvements.append(dict(first=j,nodes=k[0],grammar=encode(z)))
  result.update(second_first_variants=firsts,second_examined=count,second_histogram={str(k):v for k,v in sorted(hist.items())},second_rejections=dict(bad),improvements=improvements)
 args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__':main()
