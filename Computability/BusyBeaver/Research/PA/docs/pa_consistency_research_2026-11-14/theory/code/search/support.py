"""Portable support for the bounded AX grammar search.

The final tables are verified separately by ../verify.py. This search is
heuristic and its failure is not a lower-bound proof.
"""
from pathlib import Path
from functools import lru_cache
import itertools
import json
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import compiler as c
INC = ('leaf', 'inc', 1)
BREAK = ('leaf', 'breakTo', 1)
raw = c.raw_nodes()

def tree_word(t):
    return tree_word(t[0]) + tree_word(t[1]) if c.isnode(t) else (t,)

def encode(t):
    rules = {}
    ids = {}
    def rec(x):
        if not c.isnode(x):
            return x
        if x in ids:
            return ids[x]
        children = [rec(y) for y in x]
        key = 'g' + str(len(rules))
        rules[key] = children
        ids[x] = key
        return key
    root = rec(t)
    return {'root': root, 'rules': rules}


def apply(rows,chosen):
 aliases={a:b for a,b,acts in chosen};actions={b:acts for a,b,acts in chosen};folded={}
 for(q,bit),act in rows.items():
  if q in aliases:continue
  w,d,n=actions[q][bit]if q in actions else act
  folded[q,bit]=w,d,aliases.get(n,n)
 return folded,aliases

def localvalid(rows,folded,alias,chosen):
 for a,b,acts in chosen:
  for q,p in ((a,0),(b,1)):
   for v in(0,1):
    w,d,n=rows[q,v];target=alias.get(n,n);wanthead=1 if d else -1;expect={-1:p,0:w}
    tape={-1:p,0:v};pos=0;now=b
    for step in range(20):
     if step and pos==wanthead and now==target and tape==expect:break
     if pos not in tape:return False
     act=folded.get((now,tape[pos]))
     if act is None:return False
     w2,d2,now=act;tape[pos]=w2;pos+=1 if d2 else -1
    else:return False
 return True

def bestcompatible(rows,shape):
 ops=c.opportunities_fast(rows,shape);best=[]
 for mask in range(1<<len(ops)):
  if mask.bit_count()<len(best):continue
  chosen=[];used=set()
  for i,(a,b,choices)in enumerate(ops):
   if mask>>i&1:
    if used&{a,b}:break
    used|={a,b};chosen.append((a,b,tuple(x[0]for x in choices)))
  else:
   folded,alias=apply(rows,chosen)
   if localvalid(rows,folded,alias,chosen):
    if len(chosen)>len(best):best=chosen
 return best


def bestcompatible_all(rows,shape):
 ops=c.opportunities_fast(rows,shape)
 bound=len(c.max_matching(ops))
 variants=[[(a,b,tuple(acts)) for acts in itertools.product(*choices)] for a,b,choices in ops]
 best=bestcompatible(rows,shape)
 if len(best)==bound:return best
 for size in range(bound,len(best),-1):
  chosen=[]
  def search(i,used):
   if len(chosen)==size:
    folded,alias=apply(rows,chosen)
    return list(chosen) if localvalid(rows,folded,alias,chosen) else None
   if i==len(ops) or len(chosen)+len(ops)-i<size:return None
   a,b,_=ops[i]
   if not used&{a,b}:
    for v in variants[i]:
     chosen.append(v);answer=search(i+1,used|{a,b});chosen.pop()
     if answer is not None:return answer
   return search(i+1,used)
  found=search(0,set())
  if found is not None:return found
 return best


@lru_cache(None)
def attrs(t):
 if isinstance(t,str):return attrs(raw[t])
 if not c.isnode(t):return(0,0,0,0,t[:2]==('leaf','inc'))
 a,b=map(attrs,t);return 1+max(a[0],b[0]),a[1]+1,max(a[1]+1,a[2],b[2]),max(a[3],b[3],1+a[1]if a[4]else 0),a[4]
def nodes(t):
 out=set()
 def go(t):
  if c.isnode(t)and t not in out:out.add(t);go(t[0]);go(t[1])
 go(t);return out

def bad(t):
 out=[]
 def go(t,b=None):
  if (t=='node142'and b!=1)or(t=='node72'and b!=0):out.append(t)
  if c.isnode(t):go(t[0],0);go(t[1],1)
 go(t);return len(out)
def rotations(t):
 if c.isnode(t[0]):
  a,b=t[0];yield a,(b,t[1])
 if c.isnode(t[1]):
  b,d=t[1];yield (t[0],b),d

def repl(t,x,y):
 if t==x:return y
 return tuple(repl(z,x,y)for z in t)if c.isnode(t)else t
