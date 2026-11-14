#!/usr/bin/env python3
"""Source-conditioned five-cell overapproximation for PA196.

Uses the upstream arbitrary-natural symbolic contracts, not finite executions,
to cover every literal state along every source instruction. Unknown run lengths
are independently overapproximated, list interiors use the independently
computed radius-six blank-window closure, and the exact startup is included.
This is executable evidence; no proof-assistant certificate is claimed.
"""
from pathlib import Path
from functools import lru_cache
import argparse, hashlib, importlib.util, json, sys, time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
ALLOC=HERE
OUT=ROOT/'results/cd6_mask_refined'
TABLE=ROOT/'inputs/cd6_parent196.tm'
CONJUGACY=ROOT/'inputs/Conjugacy.lean'
FOLD=HERE/'blank_windows.py'

def load(name,path):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def need(x,m):
 if not x: raise ValueError(m)

@lru_cache(None)
def anybits(k):
 return tuple(tuple((v>>i)&1 for i in range(k)) for v in range(1<<k))

@lru_cache(None)
def prefixes(atoms,k):
 if k==0:return ((),)
 if not atoms:return anybits(k) # only hypothetical exterior; conservative
 a=atoms[0]
 if a[0]=='blank':return ((0,)*k,)
 if a[0] in ('list','opaque'):return anybits(k)
 need(a[0]=='run','Unknown atom')
 _,b,n=a
 minimum=n[0]; variable=any(n[1:])
 need(minimum>=0 and all(x>=0 for x in n),'negative length')
 choices=range(min(minimum,k),k+1) if variable else (min(minimum,k),)
 out=set()
 for size in choices:
  if size==k:out.add((b,)*k)
  else:
   out.update((b,)*size+t for t in prefixes(atoms[1:],k-size))
 return tuple(sorted(out))

class Collector:
 def __init__(self, legacy_to_dense):
  self.windows={q:set() for q in range(196)};self.mapping=legacy_to_dense
  self.steps=0;self.unary=0;self.list_calls=0
 def collect(self,q,left,right,direction):
  if q==254:return
  q=self.mapping[q]
  l=prefixes(tuple(left),2 if direction==1 else 3)
  r=prefixes(tuple(right),3 if direction==1 else 2)
  for ls in l:
   for rs in r:
    bits=tuple(reversed(ls))+rs
    need(len(bits)==5,'window width')
    self.windows[q].add(sum(v<<i for i,v in enumerate(bits)))
 def observe(self,state,table,lemmas,clock,motion):
  state.key();self.steps+=1
  self.collect(state.q,state.left,state.right,state.direction)
  src,dst=(state.right,state.left) if state.direction==1 else (state.left,state.right)
  if src[0][0]=='list':self.list_calls+=1
  elif src[0][0]=='run':
   a=src[0];w,d,q=table[state.q,a[1]]
   if q==state.q and d==state.direction:
    self.unary+=1
    # A window sees at most three symbols on either side. For a variable
    # run all n>=minimum are admitted; lengths past minimum+6 add only
    # already represented saturated interior/endpoint windows.
    ns=range(a[2][0],a[2][0]+7) if any(a[2][1:]) else [a[2][0]]
    for n in ns:
     positions=set(range(1,min(n,4))) | set(range(max(1,n-3),n))
     for i in positions:
      first=[('run',a[1],(n-i,)+(0,)*12)]+src[1:]
      second=[('run',w,(i,)+(0,)*12)]+dst
      left,right=(second,first) if d==1 else (first,second)
      self.collect(state.q,left,right,d)
  return self.original(state,table,lemmas,clock,motion)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=OUT);a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True)
 sys.path.insert(0,str(ALLOC));import symbolic_runtime as s
 s.HEADER_BASE=48
 fold=load('fold',FOLD);fold.EXPECTED_HASH=hashlib.sha256(TABLE.read_bytes()).hexdigest()
 dense_table,digest=fold.read_table(TABLE)
 text=CONJUGACY.read_text()
 import re
 native_labels=json.loads(re.search(r'def labels : List Nat := (\[[^\n]+\])',text).group(1))
 native_to_legacy={int(k):v for k,v in json.loads((ROOT/'inputs/legacy_mapping.json').read_text()).items()}
 for q in native_labels:native_to_legacy.setdefault(q,q+1000)
 legacy_to_dense={native_to_legacy[q]:i for i,q in enumerate(native_labels)}
 legacy_table={(native_to_legacy[native_labels[q]],b):(w,d,native_to_legacy[native_labels[t]]) for(q,b),(w,d,t)in dense_table.items()}
 collector=Collector(legacy_to_dense);collector.original=s.State.step
 # Prove generic list passes before instrumentation, then cover their inner
 # states using the safe independently computed blank-start invariant.
 lemmas,blocks=s.prove_blocks(legacy_table)
 list_states={ev[1][0] for block in blocks for ev in block['trace']}
 s.State.step=lambda state,table,lemmas,clock,motion: collector.observe(state,table,lemmas,clock,motion)
 start=time.monotonic();sites=json.loads((ROOT/'inputs/original.json').read_text());sites[26][1:]=['CD',6];contracts=0
 # The joint source-mask closure begins at the exact initialized source
 # store, and overapproximates every natural-valued execution.  Use only
 # its universally zero/positive coordinates here, retaining correlations
 # neither between uncertain coordinates nor between tape run lengths.
 from collections import deque
 rot=load('rot_mask',HERE/'source_graph.py')
 joint=load('joint_mask',HERE/'mask_successors.py')
 graph=rot.graph(rot.root)
 seen={(25,1)};todo=deque(seen);masks=[set() for _ in sites]
 while todo:
  pc,m=todo.popleft();masks[pc].add(m)
  for nxt in joint.successors(graph[pc],m):
   if nxt not in seen:seen.add(nxt);todo.append(nxt)
 need(all(all(nxt in seen for nxt in joint.successors(graph[pc],m)) for pc,m in seen),'mask closure')
 original_var=s.var
 skipped=0
 for i,site in enumerate(sites):
  if not masks[i]:continue
  may_positive=0;must_positive=(1<<9)-1
  for mask in masks[i]:may_positive|=mask;must_positive&=mask
  zero=((1<<9)-1)^may_positive
  for positive in ([False,True] if site[1]=='CD' and i!=26 else [False]):
   if site[1]=='CD' and ((positive and zero>>site[2]&1) or (not positive and must_positive>>site[2]&1)):
    skipped+=1;continue
   def restricted_var(slot):
    if 2<=slot<=10:
     register=slot-2
     if zero>>register&1:return s.ZERO
     if must_positive>>register&1 and not (site[1]=='CD' and register==site[2]):
      return s.add(original_var(slot),s.num(1))
    return original_var(slot)
   s.var=restricted_var
   s.case(legacy_table,lemmas,site,positive);contracts+=1
  if i%500==499:print('contracts',contracts,'windows',sum(map(len,collector.windows.values())),flush=True)
 # In the public table, exact startup lasts 58154 steps and terminates at
 # root75 on the independently specified full frame.
 tape=set();q=0;h=0
 for step in range(58402):
  mask=sum(int(h+j in tape)<<(j+2) for j in range(-2,3));collector.windows[q].add(mask)
  b=int(h in tape);w,d,q=dense_table[q,b]
  if w:tape.add(h)
  else:tape.discard(h)
  h+=d
 expected={h-1,h,h+48}
 physical=[0,0,0,0,0,0,2,0,0]+[1]*26
 p=h+49
 for v in physical:
  expected.update(range(p+1,p+v+2));p+=v+2
 need(q==75 and tape==expected,'startup frame mismatch')
 contexts,halts,nclosure=fold.blank_window_contexts(dense_table,6)
 global_windows={q:set() for q in range(196)}
 for(q,b),cases in contexts.items():
  global_windows[q].update(sum(t[i]<<(i+2)for i in range(-2,3))for t in cases)
 for state in list_states:
  q=legacy_to_dense[state];collector.windows[q].update(global_windows[q])
 raw_count=sum(map(len,collector.windows.values()))
 # Intersect two independently sound overapproximations. This removes only
 # windows ruled out by the transition-level inductive closure.
 removed={q:sorted(collector.windows[q]-global_windows[q]) for q in range(196)}
 refined={q:collector.windows[q]&global_windows[q] for q in range(196)}
 data=''.join(f'{q} {(mask>>2)&1} {mask}\n'for q in range(196)for mask in sorted(refined[q]))
 (a.output/'source_contexts.txt').write_text(data)
 missing={q:sorted(global_windows[q]-refined[q])for q in range(196)if global_windows[q]-refined[q]}
 receipt=dict(machine_sha256=digest,source_invariant_pairs=len(seen),skipped_unreachable_branches=skipped,source_contracts=contracts,symbolic_steps=collector.steps,unary_events=collector.unary,list_calls=collector.list_calls,list_interior_states_dense=sorted(legacy_to_dense[q]for q in list_states),raw_source_windows=raw_count,blank_window_closure=nclosure,global_projected_windows=sum(map(len,global_windows.values())),refined_windows=sum(map(len,refined.values())),removed_windows=missing,context_sha256=hashlib.sha256(data.encode()).hexdigest(),seconds=time.monotonic()-start)
 (a.output/'source_contexts_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:v for k,v in receipt.items()if k!='removed_windows'},indent=2))
if __name__=='__main__':main()
