#!/usr/bin/env python3
"""Allocate reassociated K219 decoder roles with a relational old-role map.

This exploratory compiler preserves the classified runtime rows, original
alias helpers, and first36 startup transitions.  Exact full primitive/runtime
and complete startup checks remain separate obligations.
"""
from pathlib import Path
from collections import defaultdict,Counter
import argparse,json,sys,time
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import lil_matrix
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'source_work'));import rotation_search as r
from grammar_search import nodes
from hardware_objective219 import model

def catalogue(T,meta):
 counts=defaultdict(Counter)
 for q,ns in meta['groups'].items():
  for n in ns:
   for bit,ch in enumerate(n):
    if r.s.leaf(ch):counts[ch,bit][T[q,bit]]+=1
 for arg,q in[(1,41),(3,17),(4,144),(5,45),(6,21)]:counts[('CD',arg),1][(1,1,q)]+=1
 out={}
 for key,acts in counts.items():
  direct=[act for act in acts if act[:2]==(key[1],1)]
  out[key]=max(direct,key=lambda x:acts[x])if direct else max(acts,key=lambda x:acts[x])
 for op,arg,q in [('CC',1,1),('CC',2,16),('CB',1,302)]:out[(op,arg),1]=(0,-1,q)
 return out,{key:set(acts)for key,acts in counts.items()}

def binding(T,tree,roles):
 """Literal whole-prefix simulation; every actual old role is allowed."""
 failures=[];allocation={}
 for p,n in iter_paths(tree):
  tape={-1:1,**{i:int(v)for i,v in enumerate(p)}};before=dict(tape);head=0;q=84
  for tick in range(10000):
   if head==len(p):break
   if head not in tape or(q,tape[head])not in T:break
   w,d,q=T[q,tape[head]];tape[head]=w;head+=d
  if head!=len(p)or tape!=before or q not in roles[n]:
   failures.append(dict(path=p,state=q,allowed=sorted(roles[n]),head=head,tape_changed=tape!=before))
  else:allocation[p]=q
 return failures,allocation

def iter_paths(n,p=''):
 if r.s.leaf(n):return
 yield p,n
 yield from iter_paths(n[0],p+'0');yield from iter_paths(n[1],p+'1')

def allocate(T,old,new,engine,limit=120):
 evaluate,meta=model(T,old,engine);live=nodes(new)
 fixed={n:set(qs)for n,qs in meta['node_states'].items()if n in live}
 newnodes=[];seen=set()
 for p,n in iter_paths(new):
  if n not in fixed and n not in seen:seen.add(n);newnodes.append(n)
 used=set().union(*fixed.values());pool=sorted(set(meta['groups'])-used)
 protected=meta['protected'];defaults,allactions=catalogue(T,meta)
 domains={n:set(pool)for n in newnodes};requirements={}
 if new not in fixed:domains[new]&={84}
 else:assert fixed[new]=={84}
 for n in newnodes:
  for q in list(domains[n]):
   req=[];valid=True
   for bit,ch in enumerate(n):
    if(q,bit)not in protected:continue
    act=T[q,bit]
    if r.s.leaf(ch):valid &= act in allactions.get((ch,bit),())
    elif ch in fixed:valid &= act[:2]==(bit,1)and act[2]in fixed[ch]
    else:
     valid &= act[:2]==(bit,1)and act[2]in domains[ch]
     req.append((ch,act[2]))
   if valid:requirements[n,q]=req
   else:domains[n].remove(q)
 changed=True
 while changed:
  changed=False;singles={next(iter(d)):n for n,d in domains.items()if len(d)==1}
  if len(singles)<sum(len(d)==1 for d in domains.values()):return None,dict(status='INCONSISTENT_SINGLETONS')
  for n in newnodes:
   for q in list(domains[n]):
    if(q in singles and singles[q]!=n)or any(t not in domains[ch]for ch,t in requirements[n,q]):domains[n].remove(q);changed=True
 report=dict(new_roles=len(newnodes),pool_size=len(pool),protected_rows=len(protected),
             empty_domains=sum(not d for d in domains.values()),domain_sizes=sorted(map(len,domains.values())),
             objective=evaluate(new),pool_protected={q:[bit for bit in(0,1)if(q,bit)in protected]for q in pool})
 if any(not d for d in domains.values()):return None,dict(status='EMPTY_DOMAIN',**report)
 choices=[(n,q)for n in newnodes for q in sorted(domains[n])];index={x:i for i,x in enumerate(choices)}
 constraints=[];lower=[];upper=[]
 for n in newnodes:
  constraints.append([(index[n,q],1)for q in domains[n]]);lower.append(1);upper.append(1)
 for q in pool:
  constraints.append([(index[n,q],1)for n in newnodes if q in domains[n]]);lower.append(0);upper.append(1)
 for n,q in choices:
  for ch,t in requirements[n,q]:
   constraints.append([(index[n,q],1),(index[ch,t],-1)]);lower.append(-np.inf);upper.append(0)
 A=lil_matrix((len(constraints),len(choices)),dtype=float)
 for i,row in enumerate(constraints):
  for j,v in row:A[i,j]+=v
 costs=np.array([-100*sum((q,bit)in protected for bit in(0,1))+q/1000 for n,q in choices])
 started=time.monotonic()
 ans=milp(costs,integrality=np.ones(len(choices)),bounds=Bounds(0,1),constraints=LinearConstraint(A.tocsc(),lower,upper),options={'time_limit':limit})if choices else None
 report.update(solver_message=ans.message if ans is not None else'NO_NEW_ROLES',solver_seconds=time.monotonic()-started,variables=len(choices),constraints=len(constraints))
 if ans is not None and ans.x is None:return None,dict(status='NO_ALLOCATION',**report)
 mapped={n:set(qs)for n,qs in fixed.items()}
 if ans is not None:
  for(n,q),x in zip(choices,ans.x):
   if x>.5:mapped[n]={q}
 assert len(mapped)==len(fixed)+len(newnodes)
 N=dict(T)
 for n in newnodes:
  q=next(iter(mapped[n]))
  for bit,ch in enumerate(n):
   if(q,bit)in protected:continue
   if r.s.leaf(ch):
    if(ch,bit)not in defaults:return None,dict(status='MISSING_LEAF_ACTION',leaf=ch,bit=bit,**report)
    N[q,bit]=defaults[ch,bit]
   else:N[q,bit]=(bit,1,min(mapped[ch]))
 assert all(N[k]==T[k]for k in protected)
 reach={0};queue=[0]
 for q in queue:
  for bit in(0,1):
   z=N[q,bit][2]
   if z!=254 and z not in reach:reach.add(z);queue.append(z)
 N={k:v for k,v in N.items()if k[0]in reach}
 failures,allocation=binding(N,new,mapped)
 report.update(status='ALLOCATED',working_states=len(N)//2,graph_removed=sorted({q for q,bit in T}-reach),binding_failures=failures,
               changes=[list(k)+list(N[k])for k in N if N[k]!=T[k]],source_metrics=r.s.metrics(new),
               allocations=[dict(state=next(iter(mapped[n])),source_path=next(p for p,x in iter_paths(new)if x==n))for n in newnodes])
 return N,report

def main():
 ap=argparse.ArgumentParser();ap.add_argument('source',type=Path);ap.add_argument('output',type=Path);ap.add_argument('--limit',type=int,default=120);a=ap.parse_args()
 p=ROOT/'baseline219/K219_Construction_2026-10-20/machine';T=r.b.read_table((p/'k219.native.tm').read_bytes())
 old=r.normalise(r.s.tree(json.loads((p/'sites219.json').read_text())));new=r.normalise(r.s.tree(json.loads(a.source.read_text())))
 engine=json.loads((ROOT/'source218/frozen_engine_rows219.json').read_text())['rows'];N,report=allocate(T,old,new,engine,a.limit)
 a.output.mkdir(exist_ok=True,parents=True);(a.output/'allocation.json').write_text(json.dumps(report,indent=2)+'\n')
 (a.output/'sites.json').write_bytes(r.s.compact(r.s.sites(new)))
 if N is not None:(a.output/'candidate.tm').write_bytes(r.b.table_bytes(N))
 print(json.dumps({k:v for k,v in report.items()if k not in('binding_failures','changes','allocations')},indent=2),flush=True)
if __name__=='__main__':main()
