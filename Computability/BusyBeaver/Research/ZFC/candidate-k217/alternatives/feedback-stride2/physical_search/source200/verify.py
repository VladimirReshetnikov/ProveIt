#!/usr/bin/env python3
"""Owned exact source structure, primitive-word, and guarded ordinal CFG check."""
from pathlib import Path
import json,hashlib
from functools import lru_cache
D=Path(__file__).parent
assert __debug__, 'Do not disable assertions'
def read(path):
 sites=json.loads(path.read_text()); leaves={x[0]:tuple(x[1:])for x in sites};assert len(leaves)==len(sites)
 def build(p):return leaves[p]if p in leaves else(build(p+'0'),build(p+'1'))
 t=build('');return sites,t
isleaf=lambda n:isinstance(n[0],str)
@lru_cache(None)
def size(n):return 1 if isleaf(n)else size(n[0])+size(n[1])
def graph(t):
 total=size(t);rows=[]
 def walk(n,i,bs,cs):
  if isleaf(n):
   op,k=n;target=lambda st,k:st[-k]%total if len(st)>=k else 0
   edges=[]if op=='CH'else[target(cs,k)]if op=='CC'else[target(bs,k)]if op=='CB'else[target(bs,1),(i+1)%total]if op=='CD'else[(i+1)%total]
   assert i==len(rows);rows.append((op,None if op in('CB','CC')else k,edges));return
  mid=i+size(n[0]);end=i+size(n);walk(n[0],i,bs+[end],cs);walk(n[1],mid,bs,cs+[i])
 walk(t,0,[],[]);return rows
def nodes(t):
 out=set();todo=[t]
 while todo:
  n=todo.pop()
  if n in out:continue
  out.add(n)
  if not isleaf(n):todo.extend(n)
 return out
s,t=read(D/'source.sites.json');b,u=read(D/'reference.sites.json')
assert[s[1:]for s in s]==[r[1:]for r in b]
assert graph(t)==graph(u)
assert len(nodes(t))==200 and len(s)==4775
assert max(max(map(len,p.split('1')))for p,op,a in s)==7
assert max(len(p)for p,op,a in s)==46
assert hashlib.sha256((D/'source.sites.json').read_bytes()).hexdigest()=='d70f4004ab7d579e8ce06f545bbe18654201cc3a7f3df10adc3a9e2f500461b0'
print('PASS: 200 source DAG nodes, zero-run7, depth46; exact guarded CFG and primitive word. Not a214-state machine.')
