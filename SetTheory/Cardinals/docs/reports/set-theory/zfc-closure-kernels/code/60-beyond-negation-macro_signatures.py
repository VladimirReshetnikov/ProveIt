"""Finite structural signatures for operation bisimulation of closed RM subtrees.

No arithmetic assumption: a signature retains each decrement register and both
branches, and only commutes increments between those tests. It includes halt,
normal exit and divergence. Intended as an engineering matcher, not a kernel proof.
"""
from functools import cache
from collections import deque

def make_signature(tree):
 leaves=[];first={}
 def walk(e,p):
  first[p]=len(leaves)
  if e[0]=='N':walk(e[1],p+'0');walk(e[2],p+'1')
  else:leaves.append((p,e))
 walk(tree,'')
 m=len(leaves)
 def inc(p):
  j=p.rfind('0')
  return first[p[:j]+'1'] if j>=0 else m
 def strip(p,k,b):
  while k:
   j=p.rfind(b)
   if j<0:raise ValueError(('unclosed',p,k,b))
   p=p[:j];k-=1
  return p
 @cache
 def seg(i,trail=()):
  # trail solely detects control-only divergence. It is not part of memo key
  # across recursive edges because this routine uses an explicit local loop.
  incs=[0]*9;seen=set()
  while i<m:
   if i in seen:return tuple(incs),('div',)
   seen.add(i);p,e=leaves[i];k=e[0]
   if k=='I':incs[e[1]]+=1;i+=1
   elif k=='D':return tuple(incs),('test',i)
   elif k=='H':return tuple(incs),('halt',)
   elif k=='B':i=inc(strip(p,e[1],'0'))
   elif k=='C':i=first[strip(p,e[1],'1')]
   else:raise ValueError(e)
  return tuple(incs),('exit',)
 entry=seg(0);queue=deque([entry[1]]);rows={}
 while queue:
  q=queue.popleft()
  if q in rows:continue
  if q[0]!='test':rows[q]=(q[0],);continue
  i=q[1];p,e=leaves[i];out=(seg(i+1),seg(inc(strip(p,1,'0'))))
  rows[q]=('D',e[1],out)
  queue.extend(target for _,target in out)
 # Deterministic partition refinement then a canonical traversal.
 colors={q:(r[:2] if r[0]=='D' else r) for q,r in rows.items()}
 for _ in range(len(rows)+1):
  palette={};new={}
  for q,row in rows.items():
   key=(row[:2],tuple((cnt,colors[tgt]) for cnt,tgt in row[2])) if row[0]=='D' else row
   if key not in palette:palette[key]=len(palette)
   new[q]=palette[key]
  if len(set(colors.values())) == len(set(new.values())):break
  colors=new
 else:raise AssertionError('refinement')
 colors=new
 representatives={}
 for q,c in colors.items():representatives.setdefault(c,q)
 root=colors[entry[1]];indices={root:0};pending=deque([root]);result=[]
 while pending:
  c=pending.popleft();row=rows[representatives[c]]
  if row[0]!='D':result.append(row);continue
  out=[]
  for count,tgt in row[2]:
   target=colors[tgt]
   if target not in indices:indices[target]=len(indices);pending.append(target)
   out.append((count,indices[target]))
  result.append((row[0],row[1],tuple(out)))
 return entry[0],tuple(result)
