#!/usr/bin/env python3
"""Bounded FT215 decoder reallocation with actual-table engine protections.
Synthesis/prefix checking only. No runtime or consistency theorem follows from
this allocator's success; every output needs independent full validation.
This conservative model pins all existing contextual aliases and their rows.
"""
from pathlib import Path
from collections import defaultdict,Counter
import argparse,json,hashlib,sys,time
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import lil_matrix
HERE=Path(__file__).resolve().parent;sys.path.insert(0,str(HERE/'vendor'))
import source_language as s,build221 as b

def paths(n,p=''):
 if s.leaf(n):return
 yield p,n
 yield from paths(n[0],p+'0');yield from paths(n[1],p+'1')
def edge(T,q,p,bit):
 tape={-1:1,**{i:int(v)for i,v in enumerate(p+str(bit))}};before=tape.copy();h=len(p);used=[]
 for _ in range(100):
  if h==len(p)+1:return(q if tape==before else None),used
  if h not in tape or(q,tape[h])not in T:return None,used
  k=q,tape[h];used.append(k);w,d,q=T[k];tape[h]=w;h+=d
 return None,used

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--remove',type=int,default=-1);ap.add_argument('--seconds',type=float,default=25);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True);tic=time.monotonic()
 T=b.read_table((HERE/'ft-frontier/machine.native.tm').read_bytes());tree=s.tree(json.loads((HERE/'ft-source.sites.json').read_text()));groups,oldpaths=b.decoder_map(T,tree)
 E={tuple(k)for k in json.loads((HERE/'ft-frontier/runtime.json').read_text())['engine_rows']};P=set(E);helper=set();aliases={q for q,ns in groups.items()if len(ns)>1};pin={n:q for q in aliases for n in groups[q]}
 for q,ps in oldpaths.items():
  for p in ps:
   n=s.subtree(tree,p)
   for bit,ch in enumerate(n):
    if not s.leaf(ch):
     z,trace=edge(T,q,p,bit);assert z is not None;helper.update(trace[1:])
 P|=helper;P|={(q,bit)for q in aliases for bit in(0,1)}
 # Keep the literal blank bootstrap through the first dispatcher visit.
 q=h=0;ones=set();bootstrap=set()
 for tick in range(10000):
  if q==84:break
  k=q,int(h in ones);bootstrap.add(k);w,d,q=T[k]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=d
 else:raise AssertionError('Bootstrap does not reach dispatcher')
 P|=bootstrap
 occ=defaultdict(list)
 for p,n in paths(tree):occ[n].append(p)
 nodes=list(occ);states=sorted({q for q,bit in T}-{a.remove});acts=defaultdict(Counter)
 for q,ns in groups.items():
  for n in ns:
   for bit,ch in enumerate(n):
    if s.leaf(ch):acts[ch,bit][T[q,bit]]+=1
 for op,arg,q in [('CC',1,1),('CC',2,16),('CB',1,302)]:acts[((op,arg),1)][(0,-1,q)]+=1
 domains={n:({pin[n]}if n in pin else set(states)-aliases)for n in nodes};reqs={}
 report={'remove':a.remove,'input_sha256':hashlib.sha256((HERE/'ft-frontier/machine.native.tm').read_bytes()).hexdigest(),'nodes':len(nodes),'existing_aliases':len(aliases),'pinned_alias_roles':len(pin),'engine_rows':len(E),'helper_rows':len(helper),'bootstrap_rows':len(bootstrap),'protected_rows':len(P),'scope':'Bounded fixed-source global allocation, with all existing contextual aliases pinned, exact observed engine rows, decoder helper rows and first bootstrap rows protected. A negative result concerns only this model. Prefix success requires independent full primitive/startup validation.'}
 def finish(status):
  report.update(status=status,seconds=time.monotonic()-tic);(a.output/'result.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items()if k not in('domains','mapping','failures','changed_rows','hall_witness')},indent=2),flush=True)
 blockers=[list(k)+list(T[k])for k in sorted(P)if k[0]==a.remove or T[k][2]==a.remove]
 if blockers:report['protected_removal_conflicts']=blockers;finish('PROTECTED_REMOVAL_CONFLICT');return
 for n in nodes:
  for q in list(domains[n]):
   if(q==84)!=(n==tree):domains[n].remove(q);continue
   rs=[];ok=True
   for bit,ch in enumerate(n):
    if(q,bit)not in P:continue
    if s.leaf(ch):
     if T[q,bit]not in acts[ch,bit]:ok=False;break
    else:
     zs=set()
     for p in occ[n]:
      z,trace=edge(T,q,p,bit)
      if z is None or any(k not in P for k in trace[1:]):ok=False;break
      zs.add(z)
     if not ok or len(zs)!=1:ok=False;break
     rs.append((ch,next(iter(zs))))
   if ok:reqs[n,q]=rs
   else:domains[n].remove(q)
 change=True
 while change:
  change=False
  for n in nodes:
   for q in list(domains[n]):
    if any(z not in domains[ch]for ch,z in reqs[n,q]):domains[n].remove(q);change=True
 report['domains']=[len(domains[n])for n in nodes]
 if any(not domains[n]for n in nodes):
  report['empty_domain_paths']=[occ[n][0]for n in nodes if not domains[n]];finish('EMPTY_DOMAIN');return
 # Independent bipartite capacity relaxation: if it already fails, output a
 # finite Hall witness, which can be checked without trusting MILP infeasibility.
 slots={q:[(q,j)for j in range(len(groups[q])if q in aliases else 1)]for q in states}
 adjacency={i:[slot for q in sorted(domains[n])for slot in slots[q]]for i,n in enumerate(nodes)}
 owner={}
 def augment(i,seen):
  for slot in adjacency[i]:
   if slot in seen:continue
   seen.add(slot)
   if slot not in owner or augment(owner[slot],seen):owner[slot]=i;return True
  return False
 for i in range(len(nodes)):augment(i,set())
 report['capacity_matching_size']=len(owner)
 if len(owner)<len(nodes):
  left=set(range(len(nodes)))-set(owner.values());right=set();todo=list(left)
  for i in todo:
   for slot in adjacency[i]:
    right.add(slot)
    if slot in owner and owner[slot]not in left:left.add(owner[slot]);todo.append(owner[slot])
  assert len(right)<len(left) and right==set(slot for i in left for slot in adjacency[i])
  report['hall_witness']={'role_count':len(left),'slot_count':len(right),'roles':[{'path':occ[nodes[i]][0],'domain_states':sorted(domains[nodes[i]])}for i in sorted(left)],'slots':sorted(right),'meaning':'These distinct internal DAG roles require distinct physical slots in this pinned-alias model, but their entire allowed union has fewer slots.'}
 choices=[(n,q)for n in nodes for q in sorted(domains[n])];idx={x:i for i,x in enumerate(choices)};rows=[];lo=[];hi=[]
 def cons(row,l,h):rows.append(row);lo.append(l);hi.append(h)
 for n in nodes:cons({idx[n,q]:1 for q in domains[n]},1,1)
 for q in states:cons({idx[n,q]:1 for n in nodes if q in domains[n]},0,len(groups[q])if q in aliases else 1)
 for n,q in choices:
  for ch,z in reqs[n,q]:cons({idx[n,q]:1,idx[ch,z]:-1},-np.inf,0)
 A=lil_matrix((len(rows),len(choices)))
 for i,row in enumerate(rows):
  for j,v in row.items():A[i,j]=v
 oldroles=defaultdict(set)
 for q,ns in groups.items():
  for n in ns:oldroles[n].add(q)
 cost=np.array([-100*sum((q,bit)in E for bit in(0,1))-(5 if q in oldroles[n]else 0)+q/1000 for n,q in choices])
 print('SOLVE',a.remove,len(choices),len(rows),flush=True);ans=milp(cost,integrality=np.ones(len(choices)),bounds=Bounds(0,1),constraints=LinearConstraint(A.tocsc(),lo,hi),options={'time_limit':a.seconds})
 report.update(solver=ans.message,variables=len(choices),constraints=len(rows),solver_status=int(ans.status))
 if ans.x is None:finish('NO_ALLOCATION');return
 mapped={n:q for(n,q),x in zip(choices,ans.x)if x>.5};assert len(mapped)==len(nodes);qnodes=defaultdict(list)
 for n,q in mapped.items():qnodes[q].append(n)
 N=dict(T)
 for q,ns in qnodes.items():
  for bit in(0,1):
   if(q,bit)in P:continue
   cs=[n[bit]for n in ns]
   if s.leaf(cs[0]):
    allowed=set(acts[cs[0],bit])
    for c in cs[1:]:allowed&=set(acts[c,bit])
    allowed={act for act in allowed if act[2]!=a.remove};assert allowed
    N[q,bit]=T[q,bit]if T[q,bit]in allowed else sorted(allowed,key=lambda x:(x[:2]!=(bit,1),x))[0]
   else:assert len(set(cs))==1;N[q,bit]=(bit,1,mapped[cs[0]])
 assert all(N[k]==T[k]for k in P)
 reach={0};todo=[0];bad=[]
 for q in todo:
  if q==a.remove:bad.append(q);continue
  for bit in(0,1):
   z=N[q,bit][2]
   if z!=254 and z not in reach:reach.add(z);todo.append(z)
 if bad:report['still_reached_removed_state']=True;finish('REMOVAL_NOT_ACHIEVED');return
 N={k:v for k,v in N.items()if k[0]in reach};fail=[]
 for p,n in paths(tree):
  tape={-1:1,**{i:int(v)for i,v in enumerate(p)}};before=tape.copy();h=0;q=84
  for tick in range(10000):
   if h==len(p):break
   if h not in tape or(q,tape[h])not in N:break
   w,d,q=N[q,tape[h]];tape[h]=w;h+=d
  if h!=len(p)or tape!=before or q!=mapped[n]:fail.append({'path':p,'expected':mapped[n],'q':q,'h':h})
 report.update(states=len(N)//2,failures=fail,changed_rows=[list(k)+list(N[k])for k in N if N[k]!=T[k]],mapping=[{'path':occ[n][0],'q':q}for n,q in mapped.items()])
 (a.output/'machine.native.tm').write_bytes(b.table_bytes(N));finish('PREFIX_PASS'if not fail else'PREFIX_FAIL')
if __name__=='__main__':main()
