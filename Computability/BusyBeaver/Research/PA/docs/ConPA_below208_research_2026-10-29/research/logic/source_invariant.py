"""Inductive zero/positive abstract interpretation of the pinned source.

Values are masks Z=1, P=2, TOP=3; an absent program point is unreachable.
The transfer is a sound overapproximation on nonnegative integers.  Saved
postfixpoint checks cover every branch, not only the worklist's execution.
"""
import json,sys,collections
from pathlib import Path
from paths import INPUTS,OUT
import source_language as L
Z,P,TOP=1,2,3
sites=json.loads((INPUTS/'sites.json').read_text());graph=L.graph_intervals(sites)
def transfer(state,kind,arg,branch):
 r=list(state)
 if kind=='increment':r[arg]=P
 elif kind=='decrement':
  if not(state[arg]&(P if branch else Z)):return None
  r[arg]=TOP if branch else Z
 return tuple(r)
def analyze():
 facts=[None]*len(sites);seed=(1,0,13,0,0,1,0,0,1)
 facts[136]=tuple(P if x else Z for x in seed);q=collections.deque([136]);updates=0
 while q:
  i=q.popleft();effect,targets=graph[i];kind=effect[0];arg=effect[1] if len(effect)>1 else None
  for branch,target in enumerate(targets):
   new=transfer(facts[i],kind,arg,branch)
   if new is None:continue
   old=facts[target];joined=new if old is None else tuple(a|b for a,b in zip(old,new))
   if joined!=old:facts[target]=joined;q.append(target);updates+=1
 # Independently check the final pre-fixed point for every source edge.
 for i,state in enumerate(facts):
  if state is None:continue
  effect,targets=graph[i];kind=effect[0];arg=effect[1] if len(effect)>1 else None
  for branch,target in enumerate(targets):
   image=transfer(state,kind,arg,branch)
   if image is not None:
    if facts[target] is None or not all(a&b==a for a,b in zip(image,facts[target])):
     raise AssertionError(('not inductive',i,target))
 counts=collections.Counter()
 for i,(path,op,arg) in enumerate(sites):
  state=facts[i]
  if state is None:counts['unreachable_sites']+=1;continue
  counts['reachable_sites']+=1
  counts['zero_positions']+=state.count(Z);counts['positive_positions']+=state.count(P)
  if op=='CD':counts[{Z:'CD_forced_zero',P:'CD_forced_positive',TOP:'CD_both'}[state[arg]]]+=1
 return {'status':'INDUCTIVE_ZERO_POSITIVE_SOURCE_INVARIANT','seed_ordinal':136,'seed':seed,
  'domain':{'Z':Z,'P':P,'TOP':TOP},'updates':updates,'counts':dict(counts),'facts':facts}
if __name__=='__main__':
 r=analyze();(OUT/'source_invariant.json').write_text(json.dumps(r,indent=2))
 print(json.dumps({k:v for k,v in r.items()if k!='facts'},indent=2))
