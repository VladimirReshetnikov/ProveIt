#!/usr/bin/env python3
"""Preserved-row allocation objective with duplicate logical decoder roles.

K219 represents (CD6,CC2) at both13 and108. Retained physical roles therefore
form a relation, not a function from syntax nodes to states. This exploratory
bound preserves that relation and all separately protected runtime rows.
"""
from pathlib import Path
from collections import defaultdict
from functools import lru_cache
import json,sys,time
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'source_work'));import rotation_search as r
from grammar_search import nodes

def startup_rows(T):
 q=0;head=0;ones=set();used=set()
 for tick in range(1000):
  if q==84:break
  bit=int(head in ones);used.add((q,bit));w,d,q=T[q,bit]
  if w:ones.add(head)
  else:ones.discard(head)
  head+=d
 assert(q,head,ones,tick)==(84,-2,{-3,0,2,3},36)
 return used

def model(T,old,engine_rows):
 groups,paths,node_states=r.mapping(T,old)
 node_states={n:frozenset(qs)for n,qs in node_states.items()}
 bypath={p:q for q,ps in paths.items()for p in ps}
 helper=set()
 for p,q in bypath.items():
  n=r.s.subtree(old,p)
  for bit,ch in enumerate(n):
   if r.s.leaf(ch):continue
   goal=bypath[p+str(bit)]
   if T[q,bit]==(bit,1,goal):continue
   tape={i:int(v)for i,v in enumerate(p+str(bit))};tape[-1]=1;before=dict(tape)
   h=len(p);st=q;used=set()
   for _ in range(100):
    if h==len(p)+1:break
    assert h in tape
    used.add((st,tape[h]));w,d,st=T[st,tape[h]];tape[h]=w;h+=d
   assert(h,st,tape)==(len(p)+1,goal,before)
   helper.update(used)
 protected=set(map(tuple,engine_rows))|helper|startup_rows(T)
 protected_states={q for q,b in protected}&set(groups)
 leaves=defaultdict(set)
 for q,ns in groups.items():
  for n in ns:
   for bit,ch in enumerate(n):
    if r.s.leaf(ch):leaves[ch,bit].add(T[q,bit])
 nondecoder=len({q for q,b in T}-set(groups))

 @lru_cache(None)
 def requirements(q,n):
  if n in node_states:return ()if q in node_states[n]else None
  if r.s.leaf(n)or q not in groups:return None
  pairs={q:n};inverse={n:q}
  for bit,ch in enumerate(n):
   if(q,bit)not in protected:continue
   act=T[q,bit]
   if r.s.leaf(ch):
    if act not in leaves[ch,bit]:return None
   else:
    if act[:2]!=(bit,1):return None
    req=requirements(act[2],ch)
    if req is None:return None
    for st,node in req:
     if st in pairs and pairs[st]!=node:return None
     if node in inverse and inverse[node]!=st:return None
     pairs[st]=node;inverse[node]=st
  return tuple(pairs.items())

 @lru_cache(None)
 def edge(q,bit,targets,suffix):
  tape={i-len(suffix):int(v)for i,v in enumerate(suffix)};tape[0]=bit;before=dict(tape);head=0
  for _ in range(100):
   if head==1:return int(q not in targets or tape!=before)
   if head not in tape or(q,tape[head])not in T:return 1
   w,d,q=T[q,tape[head]];tape[head]=w;head+=d
  return 1

 @lru_cache(None)
 def context_penalty(n,suffix='1'):
  if r.s.leaf(n):return 0
  own=0
  if n in node_states:
   choices=[]
   for q in node_states[n]:
    bad=0
    for bit,ch in enumerate(n):
     if not r.s.leaf(ch):bad+=edge(q,bit,node_states[ch],suffix)
     elif q==108 and bit==1:
      leaf_suffix=suffix+'1'
      if ch==('CC',2):bad+=int(not leaf_suffix.endswith('101'))
      elif ch==('CB',1):bad+=int(not leaf_suffix.endswith('001'))
    choices.append(bad)
   own=min(choices)
  return own+context_penalty(n[0],(suffix+'0')[-8:])+context_penalty(n[1],(suffix+'1')[-8:])

 def evaluate(new):
  live=nodes(new);fixed=set().union(*(node_states.get(n,())for n in live))
  fresh=[n for n in live if not r.s.leaf(n)and n not in node_states]
  missing=protected_states-fixed;candidate={}
  for q in missing:
   options=[]
   for i,n in enumerate(fresh):
    if n==new and q!=84:continue
    req=requirements(q,n)
    if req is not None and all(st not in fixed for st,node in req):options.append(i)
   candidate[q]=options
  matched={}
  def augment(q,seen):
   for i in candidate[q]:
    if i in seen:continue
    seen.add(i)
    if i not in matched or augment(matched[i],seen):matched[i]=q;return True
   return False
  for q in sorted(candidate,key=lambda q:len(candidate[q])):augment(q,set())
  bare=nondecoder+len(fixed)+len(fresh);overhead=len(missing)-len(matched)
  return dict(cost_lower_bound=bare+overhead,bare_cost=bare,helper_overhead=overhead,
              protected_missing=sorted(missing),unmatched_protected=sorted(missing-set(matched.values())),
              context_penalty=context_penalty(new),metrics=r.s.metrics(new))
 return evaluate,dict(groups=groups,paths=paths,node_states=node_states,protected=protected,
                      protected_states=protected_states,nondecoder=nondecoder,leaves=leaves,
                      context_penalty=context_penalty,requirements=requirements)

def main():
 import argparse
 ap=argparse.ArgumentParser();ap.add_argument('--summary',type=Path,default=ROOT/'source218/equality_compositions/summary.json');ap.add_argument('--output',type=Path,default=ROOT/'source218/composition_hardware_screen.json');a=ap.parse_args()
 p=ROOT/'baseline219/K219_Construction_2026-10-20/machine'
 T=r.b.read_table((p/'k219.native.tm').read_bytes());old=r.normalise(r.s.tree(json.loads((p/'sites219.json').read_text())))
 engine=ROOT/'source218/frozen_engine_rows219.json'
 if engine.exists():rows=json.loads(engine.read_text())['rows'];mode='COMPLETE219_CLASSIFICATION'
 else:rows=json.loads((ROOT/'root_work/frozen_engine_rows2.json').read_text())['rows']+[[302,0],[302,1]];mode='PRELIMINARY220_ROWS_PLUS302'
 evaluate,m=model(T,old,rows);base=evaluate(old);assert base['cost_lower_bound']==219 and base['context_penalty']==0,base
 records=[]
 for entry in json.loads(a.summary.read_text())['results']:
  path=ROOT/entry['output'];new=r.normalise(r.s.tree(json.loads(path.read_text())))
  record=evaluate(new);record['source']=str(path.relative_to(ROOT));records.append(record)
 records.sort(key=lambda x:(x['cost_lower_bound'],x['context_penalty'],x['metrics']['maximum_zero_run']))
 receipt=dict(status='DUPLICATE_AWARE_PRESERVED_ROW_SCREEN',engine_model=mode,baseline=base,
              decoder_states=len(m['groups']),logical_nodes=len(m['node_states']),protected_rows=len(m['protected']),
              records=records)
 a.output.write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps({k:v for k,v in receipt.items()if k!='records'},indent=2))
 for record in records[:20]:print(json.dumps(record),flush=True)
if __name__=='__main__':main()
