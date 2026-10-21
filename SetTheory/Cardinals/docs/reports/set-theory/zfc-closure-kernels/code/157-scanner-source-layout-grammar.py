#!/usr/bin/env python3
"""Search whole-source closed associativity with a five-zero address bound.

Each proposal replaces all copies of one closed ((A,B),C)/(A,(B,C)) role.
Search is heuristic; saved candidates independently check two exact CFGs.
"""
import sys,json,random,math,time,argparse,hashlib
from pathlib import Path
from functools import lru_cache
sys.dont_write_bytecode=True
LIB=Path(__file__).resolve().parent
sys.path.insert(0,str(LIB))
import source_language as s

class Grammar:
 def __init__(self):self.ns=[];self.ids={};self.bds=[];self.sz=[];self.bad=[]
 def leaf(self,i):return isinstance(self.ns[i][0],str)
 def put(self,node):
  if node in self.ids:return self.ids[node]
  i=len(self.ns);self.ids[node]=i;self.ns.append(node)
  if isinstance(node[0],str):
   o,r=node;bd=(1,0,False)if o=='CD'else(r,0,False)if o=='CB'else(0,r,False)if o=='CC'else(0,0,o=='CH')
   self.bds.append(bd);self.sz.append(1);self.bad.append((0,)*6)
  else:
   a,b=node;x,y=self.bds[a],self.bds[b]
   self.bds.append((max(x[0]-1,y[0],0),max(x[1],y[1]-1,0),x[2]or y[2]));self.sz.append(self.sz[a]+self.sz[b])
   self.bad.append(tuple((self.sz[a]if z==5 else self.bad[a][z+1])+self.bad[b][0]for z in range(6)))
  return i
 def import_tree(self,t):return self.put(tuple(t)if s.leaf(t)else(self.import_tree(t[0]),self.import_tree(t[1])))
 def export(self,i):return self.ns[i]if self.leaf(i)else tuple(self.export(x)for x in self.ns[i])
 def reachable(self,i):
  seen=set();todo=[i]
  for q in todo:
   if q in seen:continue
   seen.add(q)
   if not self.leaf(q):todo.extend(self.ns[q])
  return seen
 def replace(self,r,old,new):
  memo={old:new}
  def go(i):
   if i not in memo:memo[i]=i if self.leaf(i)else self.put(tuple(go(x)for x in self.ns[i]))
   return memo[i]
  return go(r)
 def choices(self,r):
  out=[]
  for q in self.reachable(r):
   if self.leaf(q):continue
   a,b=self.ns[q]
   if not self.leaf(a):
    A,B=self.ns[a];C=b
    if all(self.bds[x]==(0,0,False)for x in(A,B,C)):out.append((q,0,A,B,C))
   if not self.leaf(b):
    A=a;B,C=self.ns[b]
    if all(self.bds[x]==(0,0,False)for x in(A,B,C)):out.append((q,1,A,B,C))
  return out
 def initial(self,r):
  out=[]
  def walk(q,p):
   if len(out)>=37:return
   if self.leaf(q):out.append([p,*self.ns[q]])
   else:walk(self.ns[q][0],p+'0');walk(self.ns[q][1],p+'1')
  walk(r,'');return out
