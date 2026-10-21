#!/usr/bin/env python3
"""Deterministically rebuild and inspect either215 candidate. Standard library only.

Input .tm and .json files are read as inert data. This executes no incoming
programs and performs no search. The universal runtime proof is separate.
"""
import argparse,hashlib,json
from pathlib import Path

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def compact(x):return(json.dumps(x,separators=(',',':'))+'\n').encode()
def leaf(n):return isinstance(n[0],str)
def parse_table(p):
 t={}
 for line in Path(p).read_text().splitlines():
  if not line.strip()or line.startswith('#'):continue
  q,b,w,d,z=line.split();key=int(q),int(b);assert key not in t
  assert b in ['0','1']and w in ['0','1']and d in ['L','R'];t[key]=int(w),1 if d=='R'else-1,int(z)
 return t

def encode(t):return('#! start 0\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(t.items()))).encode()
def tree(sites):
 leaves={p:(op,arg)for p,op,arg in sites};assert len(leaves)==len(sites)
 def rec(p):return leaves[p]if p in leaves else(rec(p+'0'),rec(p+'1'))
 return rec('')
def flatten(t):
 out=[]
 def go(n,p):
  if leaf(n):out.append([p,*n])
  else:go(n[0],p+'0');go(n[1],p+'1')
 go(t,'');return out

def cfg(sites):
 paths=[p for p,op,k in sites];N=len(paths);start={};end={}
 for i,p in enumerate(paths):
  for j in range(len(p)+1):start.setdefault(p[:j],i);end[p[:j]]=i+1
 out=[]
 for i,(p,op,k)in enumerate(sites):
  breaks=[end[p[:j]]%N for j,b in enumerate(p)if b=='0'];continues=[start[p[:j]]for j,b in enumerate(p)if b=='1']
  stack=breaks if op in ['CD','CB']else continues
  depth=1 if op=='CD'else k if op in ['CB','CC']else 1
  target=stack[-depth]if len(stack)>=depth else 0
  edges=[]if op=='CH'else[target]if op in ['CB','CC']else[target,(i+1)%N]if op=='CD'else[(i+1)%N]
  out.append([op,None if op in ['CB','CC']else k,edges])
 return out

