#!/usr/bin/env python3
"""New authored builder: collision-free weights and the Sun ten-integer tail.
Reads upstream JSON solely as mathematical data; executes no upstream code.
"""
from pathlib import Path
import json, hashlib
from collections import Counter
ROOT=Path(__file__).resolve().parent
class DAG:
 def __init__(self):self.nodes=[];self.cache={};self.pows={};self.names={}
 def leaf(self,k,x):
  key=(k,x)
  if key not in self.cache:
   self.cache[key]=len(self.nodes);self.nodes.append({'kind':k,('value' if k=='literal' else 'name'):x})
  return self.cache[key]
 def lit(self,x):return self.leaf('literal',x)
 def op(self,k,a,b):
  if k in ('add','mul') and a>b:a,b=b,a
  va=self.nodes[a].get('value');vb=self.nodes[b].get('value')
  if va is not None and vb is not None:return self.lit(va+vb if k=='add' else va-vb if k=='sub' else va*vb)
  if k=='add':
   if va==0:return b
   if vb==0:return a
  if k=='sub' and vb==0:return a
  if k=='mul':
   if va==0 or vb==0:return self.lit(0)
   if va==1:return b
   if vb==1:return a
  key=(k,a,b)
  if key not in self.cache:
   self.cache[key]=len(self.nodes);self.nodes.append({'kind':k,'left':a,'right':b})
  return self.cache[key]
 def add(self,*xs):
  r=self.lit(0)
  for x in xs:r=self.op('add',r,x)
  return r
 def mul(self,*xs):
  r=self.lit(1)
  for x in xs:r=self.op('mul',r,x)
  return r
 def sub(self,a,b):return self.op('sub',a,b)
 def pow(self,x,n):
  if n==0:return self.lit(1)
  if n==1:return x
  if (x,n) not in self.pows:
   p=self.pow(x,n//2);r=self.mul(p,p)
   self.pows[x,n]=self.mul(r,x) if n%2 else r
  return self.pows[x,n]
 def name(self,n,x):self.names[n]=x;return x
 def export(self,out):
  used=set()
  def visit(i):
   if i in used:return
   used.add(i);n=self.nodes[i]
   if 'left'in n:visit(n['left']);visit(n['right'])
  visit(out);ids={old:new for new,old in enumerate(sorted(used))};nodes=[]
  for i in sorted(used):
   n=dict(self.nodes[i])
   if 'left'in n:n['left']=ids[n['left']];n['right']=ids[n['right']]
   nodes.append(n)
  return nodes,ids[out],{k:ids[v] for k,v in self.names.items() if v in ids}
def geom(d,B,n):
 if n==0:return d.lit(1),d.lit(0)
 if n==1:return B,d.lit(1)
 p,s=geom(d,B,n//2);p2=d.mul(p,p);s2=d.mul(s,d.add(d.lit(1),p))
 return (d.mul(p2,B),d.add(s2,p2)) if n%2 else (p2,s2)

# Release contains only DAG and geom helpers; inactive exploratory main omitted.
