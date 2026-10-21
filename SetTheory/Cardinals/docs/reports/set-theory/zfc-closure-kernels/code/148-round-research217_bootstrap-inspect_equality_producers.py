#!/usr/bin/env python3
"""Owned narrow producer/liveness inspection, without allocation or synthesis."""
from pathlib import Path
import collections,hashlib,json,sys
D=Path(__file__).resolve().parent;ROOT=D.parent
sys.path.insert(0,str(ROOT/'research218_published_encoding'));import audit_construction as A
p=ROOT/'latest218_baseline/candidate-k218/sites218.json';sites=json.loads(p.read_text());t=A.P.tree(sites);cfg=A.continuation_cfg(t);facts=json.loads((ROOT/'research218_source/invariant_facts.json').read_text());pred=collections.defaultdict(list)
for i,(op,arg,targets)in enumerate(cfg):
 for guard,j in enumerate(targets):pred[j].append((i,guard))
def image(mask,delta):
 out=0
 for a in range(10):
  if mask>>a&1:
   for n in([a]if a<8 else[a,a+2]):
    if n+delta>=0:
     v=n+delta;out|=1<<(v if v<8 else 8+v%2)
 return out
def incoming(start,end):
 out=[]
 for i,g in pred[start]:
  if start<=i<end:continue
  f=facts[i].copy();op,a,_=cfg[i]
  if op=='CD':
   selected=f[a]&(~1 if g else 1)
   if not selected:continue
   f[a]=image(selected,-1)if g else 1
  elif op=='CI':f[a]=image(f[a],1)
  out.append(dict(predecessor=i,guard=g,register_masks=f))
 return out
ranges=[('AX first duplicate',4563,4567),('AX second retained c transfer',4579,4582),('NIP constant one',4598,4599),('MP computed implication transfer',4705,4708)]
entries=[]
for name,lo,hi in ranges:
 edges=incoming(lo,hi)
 assert edges and all(e['register_masks'][6]==1 for e in edges),(name,edges)
 if lo!=4563:assert all(e['register_masks'][3]==1 for e in edges),(name,edges)
 entries.append(dict(name=name,range=[lo,hi],sites=sites[lo:hi],external_edges=edges))
assert all(not(o in('CI','CD')and a==5)for p,o,a in sites[4125:4567])
assert all(not(o in('CI','CD')and a==3)for p,o,a in sites[4151:4563])
assert sites[4124][1:]==['CI',5]and sites[4150][1:]==['CI',3]
E=A.at(t,'11110')
def rename(n,mapping):
 if A.P.leaf(n):return(n[0],mapping.get(n[1],n[1]))if n[0]in('CI','CD')else n
 return(rename(n[0],mapping),rename(n[1],mapping))
E35=rename(E,{5:3,6:5});E65=rename(E,{5:6,6:5})
result=dict(status='EXACT_PRODUCER_LIVENESS_INSPECTION',source_sha256=hashlib.sha256((ROOT/'latest218_baseline/candidate-k218/sites218.json').read_bytes()).hexdigest(),entries=entries,original_E=E,recolored_E35=E35,swapped_E65=E65,transfer_free_edits=[dict(comparison='AX second',producer_index=4580,old=['CI',6],new=['CI',3],equality_interval=[4585,4595]),dict(comparison='NIP',producer_index=4598,old=['CI',6],new=['CI',3],equality_interval=[4599,4609]),dict(comparison='MP',producer_index=4706,old=['CI',6],new=['CI',3],equality_interval=[4708,4718])],first_AX_obstruction=dict(cache_last_restore=4124,selector_last_restore=4150,selector_last_drain=4563,first_equality=4567,no_cache_access_interval=[4125,4567],no_selector_access_interval=[4151,4563],direct_rename_counterexample='Changing4565 fromCI6 toCI3 makes the loop4563..4566 preserve any positiveR3 each iteration while increasingR7. Thus this direct rename diverges rather than retainingc.'),possible_mixed_source='Use E65 at the first AX equality and E35 at the other three comparisons with the three producer edits. This uses equality symmetry and adds no primitive transfer leaves, but creates two shared equality shapes instead of one. No cost or compiler correctness is claimed.',scope='Liveness and exact source contracts only. No source enumeration, allocator call, candidate runtime or blank-start check. Old301 may cease to have its old decoder role if all four old E occurrences are replaced; actual row removal/state cost must be independently allocated and verified.')
(D/'EQUALITY_PRODUCER_LIVENESS.json').write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items()if k not in('entries','original_E','recolored_E35','swapped_E65')})
