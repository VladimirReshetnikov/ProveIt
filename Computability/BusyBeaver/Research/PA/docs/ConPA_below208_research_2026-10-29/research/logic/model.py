"""Build logically equivalent cover emitters, then optimize closed association.
Every variant uses the same inherited arithmetic macro contracts. Source trees
are candidates only until compiled, runtime checked, and bootstrapped.
"""
import sys,json,random,heapq
from pathlib import Path
from functools import lru_cache
import source_language as s,source_splice as sp
from paths import INPUTS,OUT
K=INPUTS/"k215_sites.json"
old=s.tree(json.loads((INPUTS/"sites.json").read_text()));kt=s.tree(json.loads(K.read_text()))
RANGES={'a':(26,52),'b':(52,78),'c':(107,133),'I':(78,105),'Q':(78,107),'R':(695,723),'N':(995,1042)}
macros={x:sp.serial(sp.closed_forest(kt,*rg))for x,rg in RANGES.items()}
known=sp.nodes(old);root=OUT/'variants';root.mkdir(exist_ok=True)
I=lambda a,b:('I',a,b);Q=lambda a,b:('Q',a,b);R=lambda a,b:('R',a,b);N=lambda a:('N',a)
def tokens(x):
 if isinstance(x,str):return[x]
 return sum((tokens(v)for v in x[1:]),[])+[x[0]]

# Intern full primitive trees once, then optimize only small integer node IDs.
ids={};nodes=[];shapes=[];novel=[]
def intern(n):
 if s.leaf(n): key=n
 else:key=(intern(n[0]),intern(n[1]))
 if key not in ids:
  k=len(nodes);ids[key]=k;nodes.append(key)
  if isinstance(key[0],str):shapes.append((0,0,0))
  else:
   a,b=key;da,za,ma=shapes[a];db,zb,mb=shapes[b]
   shapes.append((1+max(da,db),1+za,max(1+za,ma,mb)))
 return ids[key]
intern(old)
known_ids=set(range(len(nodes)))
macro_ids={k:intern(v)for k,v in macros.items()}
@lru_cache(None)
def newset(k):
 if k in known_ids:return frozenset()
 a,b=nodes[k];return frozenset({k})|newset(a)|newset(b)
def pair(a,b):
 key=(a,b)
 if key not in ids:
  k=len(nodes);ids[key]=k;nodes.append(key)
  da,za,ma=shapes[a];db,zb,mb=shapes[b]
  shapes.append((1+max(da,db),1+za,max(1+za,ma,mb)))
 return ids[key]
@lru_cache(None)
def expand(k):
 n=nodes[k]
 return n if isinstance(n[0],str)else(expand(n[0]),expand(n[1]))
