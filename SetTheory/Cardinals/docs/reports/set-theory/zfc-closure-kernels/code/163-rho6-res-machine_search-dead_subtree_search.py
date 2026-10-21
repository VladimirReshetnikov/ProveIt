#!/usr/bin/env python3
"""Exhaustive bounded structural replacement census; Python standard library.

This script trusts the supplied dead-prefix choice. It does not prove source
unreachability. See the separate source invariant and main report for that.
"""
import gzip, json, sys, time
from pathlib import Path
p=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('baseline217.sites.json.gz')
rows=json.loads(gzip.decompress(p.read_bytes()) if p.suffix=='.gz' else p.read_bytes())
leaves={p:(o,a) for p,o,a in rows}
def tree(p=''):
 return leaves[p] if p in leaves else (tree(p+'0'),tree(p+'1'))
D=[];ids={}
def intern(t):
 key=t if isinstance(t[0],str) else (intern(t[0]),intern(t[1]))
 if key not in ids:ids[key]=len(D);D.append(key)
 return ids[key]
root=intern(tree());N=len(D)
def replace(q,path,value):
 if not path:return value
 a,b=D[q]
 if path[0]=='0':a=replace(a,path[1:],value)
 else:b=replace(b,path[1:],value)
 key=(a,b)
 if key not in ids:ids[key]=len(D);D.append(key)
 return ids[key]
def count(root):
 todo=[root];seen=set()
 while todo:
  q=todo.pop()
  if q in seen:continue
  seen.add(q)
  if isinstance(D[q][0],int):todo.extend(D[q])
 return len(seen)
prefixes=['11101001011001101','111111001'];start=time.monotonic();best=N;single=0;paired=0
first=[]
for value in range(N):
 q=replace(root,prefixes[0],value);first.append(q);best=min(best,count(q));single+=1
 q=replace(root,prefixes[1],value);best=min(best,count(q));single+=1
for a in range(N):
 for b in range(N):
  q=replace(first[a],prefixes[1],b);best=min(best,count(q));paired+=1
print(json.dumps({'scope':'Arbitrary existing-type replacements at the two specified prefixes; structural count only','original_types':N,'single_replacements':single,'paired_replacements':paired,'minimum_dag_nodes':best,'seconds':time.monotonic()-start},indent=2))
