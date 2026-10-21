"""Interned source-tree operations for the bounded rotation searches.

This is the small source-structure portion of the research discovery driver.
The ordinary source language and physical prefix reader are the pinned upstream
modules bundled with this packet.
"""
from pathlib import Path
from functools import lru_cache
import sys

PACKET=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(PACKET/'upstream/portable'))
import source_language as s
import build221 as b

NODES=[]
IDS={}
def intern(node):
 if node not in IDS:IDS[node]=len(NODES);NODES.append(node)
 return IDS[node]
def pack(t):return intern(t if s.leaf(t) else (pack(t[0]),pack(t[1])))
def isleaf(n):return isinstance(NODES[n][0],str)
@lru_cache(None)
def unpack(n):return NODES[n] if isleaf(n) else (unpack(NODES[n][0]),unpack(NODES[n][1]))
@lru_cache(None)
def boundary(n):
 x=NODES[n]
 if isleaf(n):
  return (1,0,False) if x[0]=='CD' else (x[1],0,False) if x[0]=='CB' else (0,x[1],False) if x[0]=='CC' else (0,0,x[0]=='CH')
 a,c=map(boundary,x)
 return max(max(a[0]-1,0),c[0]),max(a[1],max(c[1]-1,0)),a[2] or c[2]
def replace(n,x,y,memo):
 if n in memo:return memo[n]
 if n==x:r=y
 elif isleaf(n):r=n
 else:r=intern(tuple(replace(i,x,y,memo) for i in NODES[n]))
 memo[n]=r
 return r
