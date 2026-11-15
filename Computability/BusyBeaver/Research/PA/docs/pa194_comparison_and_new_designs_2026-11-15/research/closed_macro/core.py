from pathlib import Path
import json,sys,collections,functools,time
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'vendor'))
import build as b
sys.path.insert(0,str(ROOT/'vendor'))
from search_support import proposed_folds
raw,nodes,ax,sites,ins,parent=b.load_inputs()
@functools.lru_cache(None)
def expand(t):
 if isinstance(t,str):return expand(ax if t=='x67' else nodes[t])
 if t[0]=='leaf':return t
 return tuple(expand(x) for x in t)
@functools.lru_cache(None)
def boundary(t):
 t=expand(t)
 if t[0]=='leaf':
  return (1,0) if t[1]=='dec' else (t[2],0) if t[1]=='breakTo' else (0,t[2]) if t[1]=='continueTo' else (0,0)
 a,c=map(boundary,t)
 return max(a[0]-1,c[0],0), max(a[1],c[1]-1,0)
entries=collections.defaultdict(set); actions=collections.defaultdict(set); seen=set()
def walk(t,q,h):
 t=expand(t)
 if (t,q,h) in seen:return
 seen.add((t,q,h));entries[t,h].add(q)
 if t[0]=='leaf':return
 for bit,c in enumerate(t):
  w,d,n=raw[q,bit]
  if c[0]=='leaf':actions[c,bit].add((w,d,n))
  if w==bit and d and n!=b.HALT:walk(c,n,bit)
walk('node172',84,1)
# Only unambiguous leaf rows are used; no guessed changes to arithmetic boxes.
def synthesize(nnodes):
 @functools.lru_cache(None)
 def exp(t):
  if isinstance(t,str):return exp(ax if t=='x67' else nnodes[t])
  if t[0]=='leaf':return t
  return tuple(exp(x) for x in t)
 rows=dict(raw);ids={};signatures={}
 for q,_ in rows:signatures[rows[q,0],rows[q,1]]=q
 def action(t,h):
  t=exp(t)
  options=entries.get((t,h),set())
  if options:return h,True,min(options)
  if t[0]=='leaf':
   a=actions.get((t,h),set())
   if len(a)==1:return next(iter(a))
   if t[1]=='continueTo':return (0,False,1) if t[2]==1 else (0,False,16) if t[2]==2 else (1,False,73)
   if t[1]=='breakTo' and t[2]==1:return (0,False,302)
   targets={'inc':{0:14,1:61,2:56,3:161,4:71,5:63,6:13,7:82,8:39},'dec':{0:14,1:41,2:56,3:17,4:144,5:45,6:21,7:62,8:39}}
   if t[1] in targets:return (h,True,targets[t[1]][t[2]])
   raise ValueError(('ambiguous leaf',t,h))
  if (t,h) in ids:return h,True,ids[t,h]
  acts=action(t[0],0),action(t[1],1)
  q=signatures.get(acts)
  if q is None:
   q=4000+len(ids);ids[t,h]=q;signatures[acts]=q
   rows[q,0],rows[q,1]=acts
  return h,True,q
 rt=exp('node172')
 a0,a1=action(rt[0],0),action(rt[1],1)
 rows[84,0],rows[84,1]=a0,a1
 return b.reachable(rows)

def rotations(t):
 if isinstance(t,str) or t[0]=='leaf':return
 a,c=t
 if not isinstance(c,str) and c[0]!='leaf':
  y,z=c
  if all(boundary(x)==(0,0) for x in (a,y,z)):yield ((a,y),z)
 elif isinstance(c,str):
  ct=nodes[c]
  if ct[0]!='leaf':
   y,z=ct
   if all(boundary(x)==(0,0) for x in (a,y,z)):yield ((a,y),z)
 if not isinstance(a,str) and a[0]!='leaf':
  x,y=a
  if all(boundary(t)==(0,0) for t in (x,y,c)):yield (x,(y,c))
 elif isinstance(a,str):
  at=nodes[a]
  if at[0]!='leaf':
   x,y=at
   if all(boundary(t)==(0,0) for t in (x,y,c)):yield (x,(y,c))

def candidate(nn):
 ss,ii=b.source(nn,ax)
 if ii!=ins:return None
 rr=synthesize(nn);folds=proposed_folds(rr)
 return len(rr)//2-len(folds),rr,ss,folds

assert synthesize(nodes)==raw

name_q={n:next(iter({q for (t,h),qs in entries.items() if t==expand(n) for q in qs})) for n in nodes if len({q for (t,h),qs in entries.items() if t==expand(n) for q in qs})==1}
q_names=collections.defaultdict(list)
for n,q in name_q.items():q_names[q].append(n)
leaf_targets={'inc':{0:14,1:61,2:56,3:161,4:71,5:63,6:13,7:82,8:39},'dec':{0:14,1:41,2:56,3:17,4:144,5:45,6:21,7:62,8:39}}
def synth_local(name,tree):
 q0=name_q[name]
 if len(q_names[q0])!=1:raise ValueError(('sharedentry',name,q_names[q0]))
 rows=dict(raw);ids={};sigs={(rows[q,0],rows[q,1]):q for q,_ in rows if q!=q0};qq=4000
 def action(t,bit):
  nonlocal qq
  if isinstance(t,str):
   if t in name_q:return bit,True,name_q[t]
   t=nodes[t]
  if t[0]=='leaf':
   if t[1] in leaf_targets:return bit,True,leaf_targets[t[1]][t[2]]
   if t[1]=='continueTo':return (0,False,1) if t[2]==1 else (0,False,16) if t[2]==2 else (1,False,73)
   if t[1]=='breakTo' and t[2]==1:return 0,False,302
   if t[1]=='halt':return bit,True,b.HALT
   raise ValueError(t)
  acts=action(t[0],0),action(t[1],1)
  if acts in sigs:return bit,True,sigs[acts]
  q=qq;qq+=1;rows[q,0],rows[q,1]=acts;sigs[acts]=q
  return bit,True,q
 rows[q0,0],rows[q0,1]=action(tree[0],0),action(tree[1],1)
 return b.reachable(rows)

