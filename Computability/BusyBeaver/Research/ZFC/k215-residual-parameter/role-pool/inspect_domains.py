#!/usr/bin/env python3
"""Bounded own row-protected allocator. Synthesis/prefix evidence, not runtime proof.
Derived from the source-read allocate219.py/model and exact decoder prefix interpreter.
The old engine classification is an inherited synthesis filter, not current verification.
"""
from pathlib import Path
from collections import defaultdict,Counter
from functools import lru_cache
from types import SimpleNamespace
import argparse,json,hashlib,time
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import lil_matrix
import source_language as s
import source_splice as sp
import build221 as b
K=Path('/home/codex/.codex/worktrees/ec20/Proofs/Computability/BusyBeaver/Research/ZFC')
ENGINE=Path('/tmp/zfc-intake189/root/recovered/ZFC_218_Research_2026-10-20/ZFC_218_Research_2026-10-20/research/source218/frozen_engine_rows219.json')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def paths(n,p=''):
 if s.leaf(n):return
 yield p,n
 yield from paths(n[0],p+'0');yield from paths(n[1],p+'1')
def edge(T,q,p,bit):
 tape={-1:1,**{i:int(v)for i,v in enumerate(p+str(bit))}};before=dict(tape);h=len(p);used=[]
 for _ in range(100):
  if h==len(p)+1:return (q if tape==before else None),used
  if h not in tape or(q,tape[h])not in T:return None,used
  k=(q,tape[h]);used.append(k);w,d,q=T[k];tape[h]=w;h+=d
 return None,used

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--limit',type=int,default=30);ap.add_argument('--fresh',type=int,default=0);a=ap.parse_args()
 a.output.mkdir(parents=True,exist_ok=False)
 table=K/'candidate-k215/k215.native.tm'
 src=K/'candidate-k215/sites215.json'
 T=b.read_table(table.read_bytes());old=s.tree(json.loads(src.read_text()));new=s.tree(json.loads(a.source.read_text()))
 assert sha(table)=='9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2'
 assert sha(src)=='17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
 original=dict(T);assert T[81,0]==(0,-1,111) # Accepted215 already contains the reviewed repair.
 assert [T[k]for k in[(111,0),(111,1),(104,0),(128,0)]]==[(0,1,104),(1,1,128),(0,1,123),(0,1,21)]
 groups,oldpaths=b.decoder_map(T,old);oldstates=defaultdict(set)
 for q,ns in groups.items():
  for n in ns:oldstates[n].add(q)
 occ=defaultdict(list)
 for p,n in paths(new):occ[n].append(p)
 @lru_cache(None)
 def compatible(n,p,q):
  if q not in oldstates.get(n,()):return False
  for bit,ch in enumerate(n):
   if s.leaf(ch):
    # State108's compressed return inspects the preceding selector bits.
    if q==108 and bit==1:
     required={'CC':'101','CB':'001'}.get(ch[0])
     if required is not None and not ('1'+p+'1').endswith(required):return False
    continue
   z,_=edge(T,q,p,bit)
   if z is None or not compatible(ch,p+str(bit),z):return False
  return True
 fixed={};incompatible=[]
 for n,ps in occ.items():
  options={q for q in oldstates.get(n,())if all(compatible(n,p,q)for p in ps)}
  if options:fixed[n]=options
  elif n in oldstates:incompatible.append({'path':ps[0],'size':sp.size(n),'states':sorted(oldstates[n])})
 newnodes=[n for n in occ if n not in fixed]
 used=set().union(*fixed.values()) if fixed else set()
 pool=sorted({q for q,bit in T}-used)+list(range(500,500+a.fresh))
 protected={tuple(k)for k in json.loads(ENGINE.read_text())['rows']if tuple(k)in T}
 protected.discard((92,1));protected|={(81,0),(111,0),(111,1),(104,0),(128,0)}
 # Protect intermediate rows used by each retained old contextual decoder role.
 helper=set()
 for n,qs in fixed.items():
  for p in occ[n]:
   for q in qs:
    for bit,ch in enumerate(n):
     if s.leaf(ch):continue
     z,trace=edge(T,q,p,bit);assert z is not None
     helper.update(trace[1:])
 protected|=helper
 leafacts=defaultdict(Counter)
 for q,ns in groups.items():
  for n in ns:
   for bit,ch in enumerate(n):
    if s.leaf(ch):leafacts[ch,bit][T[q,bit]]+=1
 defaults={}
 for key,acts in leafacts.items():
  direct=[act for act in acts if act[:2]==(key[1],1)]
  defaults[key]=max(direct or acts,key=lambda act:acts[act])
 # Known unchanged canonical return entries from accepted runtime.
 for op,arg,q in [('CC',1,1),('CC',2,16),('CB',1,302)]:
  key=((op,arg),1)
  if key in leafacts:defaults[key]=(0,-1,q);leafacts[key][defaults[key]]+=1
 domains={n:set(pool)for n in newnodes};reqs={}
 if new in domains:domains[new]&={84}
 else:assert fixed[new]=={84}
 for n in newnodes:
  for q in list(domains[n]):
   valid=True;req=[]
   for bit,ch in enumerate(n):
    if(q,bit)not in protected:continue
    act=T[q,bit]
    if s.leaf(ch):valid &= act in leafacts.get((ch,bit),())
    elif act[:2]!=(bit,1):valid=False
    elif ch in fixed:valid &= act[2]in fixed[ch]
    else:req.append((ch,act[2]))
   if valid:reqs[n,q]=req
   else:domains[n].remove(q)
 changed=True
 while changed:
  changed=False
  for n in newnodes:
   for q in list(domains[n]):
    if any(t not in domains[ch]for ch,t in reqs[n,q]):domains[n].remove(q);changed=True
 receipt={'status':'PENDING','scope':'Synthesis and complete literal decoder prefix binding only; engine protections are inherited synthesis filters. No primitive, all-natural runtime, blank startup, calibration or candidate acceptance claimed.','source':str(a.source),'source_sha256':sha(a.source),'table':str(table),'table_sha256':sha(table),'old_source_sha256':sha(src),'engine_filter':{'path':str(ENGINE),'sha256':sha(ENGINE),'not_current_runtime_proof':True},'native_repair':'Already present in accepted215; no pre-allocation mutation','new_nodes':len(newnodes),'fixed_nodes':len(fixed),'fixed_states':len(used),'pool':pool,'protected_rows':len(protected),'helpers':len(helper),'incompatible_old':incompatible,'domain_sizes':[len(domains[n])for n in newnodes],'metrics':s.metrics(new),'code_sha256':sha(Path(__file__))}
 def finish():
  (a.output/'allocation.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:v for k,v in receipt.items()if k not in('assignments','changed_rows','binding_failures','incompatible_old')},indent=2),flush=True)
 if any(not d for d in domains.values()):receipt['status']='EMPTY_DOMAIN';finish();return
 union=set().union(*domains.values())
 report={'status':'STATIC_DOMAIN_CENSUS_NO_SOLVER_INVOCATION','source_sha256':sha(a.source),'allocator_basis_sha256':sha(Path(__file__).with_name('allocate_from215.py')),'new_roles':len(newnodes),'eligible_state_union':sorted(union),'eligible_state_count':len(union),'simple_distinct_assignment_shortfall':max(0,len(newnodes)-len(union)),'all_old_pool_states':pool,'never_eligible_states':sorted(set(pool)-union),'domains':[{'path':occ[n][0],'leaves':sp.size(n),'states':sorted(domains[n])}for n in newnodes],'protected_masks':{str(q):[bit for bit in(0,1)if(q,bit)in protected]for q in pool},'scope':'Own pre-solver metadata prefix only, no MILP call or table construction. This is a necessary-condition obstruction for this retained-role/row policy, not a global state lower bound.'}
 (a.output/'domain-census.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items()if k not in('domains','protected_masks')},indent=2));return
if __name__=='__main__':main()
