#!/usr/bin/env python3
"""Experimental global role allocation with frozen engine/helper rows.
All source occurrences constrain protected contextual decoder edges. Synthesis only.
"""
from pathlib import Path
from collections import defaultdict,Counter
from itertools import combinations
import sys,json,hashlib,argparse,time
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import lil_matrix
K=Path(__file__).resolve().parent/'inputs'
sys.path.insert(0,str(Path(__file__).resolve().parent/'vendor'))
import source_language as s,build221 as b

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
 ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--seconds',type=int,default=60);ap.add_argument('--seed',type=int,default=0);a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=False)
 table=K/'k215.native.tm';oldsrc=K/'sites215.json';T=b.read_table(table.read_bytes());old=s.tree(json.loads(oldsrc.read_text()));new=s.tree(json.loads(a.source.read_text()));groups,oldpaths=b.decoder_map(T,old)
 P={tuple(k)for k in json.loads((K/'frozen_engine_rows219.json').read_text())['rows']if tuple(k)in T};P.discard((92,1));P|={(81,0),(111,0),(111,1),(104,0),(128,0)}
 helper=set()
 for q,ps in oldpaths.items():
  for p in ps:
   n=s.subtree(old,p)
   for bit,ch in enumerate(n):
    if not s.leaf(ch):
     z,trace=edge(T,q,p,bit);assert z is not None;helper.update(trace[1:])
 P|=helper
 P|={(q,bit)for q in groups for bit in(0,1)if T[q,bit][:2]!=(bit,1)}
 occ=defaultdict(list)
 for p,n in paths(new):occ[n].append(p)
 nodes=list(occ);nid={n:i for i,n in enumerate(nodes)};states=sorted({q for q,bit in T});aliases={q for q,ns in groups.items() if len(ns)>1}
 acts=defaultdict(Counter)
 for q,ns in groups.items():
  for n in ns:
   for bit,ch in enumerate(n):
    if s.leaf(ch):acts[ch,bit][T[q,bit]]+=1
 for op,arg,q in [('CC',1,1),('CC',2,16),('CB',1,302)]:acts[((op,arg),1)][(0,-1,q)]+=1
 defaults={k:max([x for x in v if x[:2]==(k[1],1)]or list(v),key=lambda x:v[x])for k,v in acts.items()}
 aliasnode=(('CD',6),('CC',2))
 domains={n:({13}if n==aliasnode else set(states))for n in nodes};reqs={};stats=Counter()
 for n in nodes:
  for q in list(domains[n]):
   if(q==84)!=(n==new):domains[n].remove(q);continue
   req=[];valid=True
   for bit,ch in enumerate(n):
    if(q,bit)not in P:continue
    if s.leaf(ch):
     if T[q,bit]not in acts[ch,bit]:valid=False;break
     if q==108 and bit==1:
      suf={'CC':'101','CB':'001'}.get(ch[0]);valid=valid and(suf is None or all(('1'+p+'1').endswith(suf)for p in occ[n]))
    else:
     zs=set()
     for p in occ[n]:
      z,trace=edge(T,q,p,bit)
      if z is None or any(k not in P for k in trace[1:]):valid=False;break
      if z==108 and ch==aliasnode:
       if not ('1'+p+str(bit)+'1').endswith('101'):valid=False;break
       z=13
      zs.add(z)
     if not valid:break
     if len(zs)!=1:valid=False;break
     req.append((ch,next(iter(zs))))
   if valid:reqs[n,q]=req
   else:domains[n].remove(q)
 change=True
 while change:
  change=False
  for n in nodes:
   for q in list(domains[n]):
    if any(z not in domains[ch]for ch,z in reqs[n,q]):domains[n].remove(q);change=True
 summary={'nodes':len(nodes),'protected_rows':len(P),'helper_rows':len(helper),'domains':[len(domains[n])for n in nodes]}
 if old==new:
  canon={n:min(q for q,ns in groups.items()if n in ns)for n in nodes}
  print('IDENTITY_BAD_DOMAINS',[(q,occ[n][0])for n,q in canon.items()if q not in domains[n]],flush=True)
  print('IDENTITY_BAD_REQS',[(q,z,canon[ch],occ[n][0])for n,q in canon.items()if(n,q)in reqs for ch,z in reqs[n,q]if canon[ch]!=z],flush=True)
 if any(not domains[n]for n in nodes):summary['status']='EMPTY_DOMAIN';(a.output/'result.json').write_text(json.dumps(summary,indent=2));print(json.dumps(summary));return
 choices=[(n,q)for n in nodes for q in sorted(domains[n])];idx={k:i for i,k in enumerate(choices)};rows=[];lo=[];hi=[]
 def cons(d,l,h):rows.append(d);lo.append(l);hi.append(h)
 for n in nodes:cons({idx[n,q]:1 for q in domains[n]},1,1)
 for n,q in choices:
  for ch,z in reqs[n,q]:cons({idx[n,q]:1,idx[ch,z]:-1},-np.inf,0)
 for q in states:
  ns=[n for n in nodes if q in domains[n]]
  if q not in aliases:cons({idx[n,q]:1 for n in ns},0,1);continue
  cons({idx[n,q]:1 for n in ns},0,len(groups[q]))
  for n,m in combinations(ns,2):
   ok=True
   for bit in (0,1):
    if(q,bit)in P:continue
    c,d=n[bit],m[bit]
    if s.leaf(c)and s.leaf(d):ok=bool(set(acts[c,bit])&set(acts[d,bit]))
    else:ok=(c==d)
    if not ok:break
   if not ok:cons({idx[n,q]:1,idx[m,q]:1},-np.inf,1)
 A=lil_matrix((len(rows),len(choices)))
 for i,row in enumerate(rows):
  for j,v in row.items():A[i,j]=v
 rng=np.random.default_rng(a.seed)
 oldroles=defaultdict(set)
 for q,ns in groups.items():
  for n in ns:oldroles[n].add(q)
 cost=np.array([-100*sum((q,bit)in P for bit in(0,1))-(5 if q in oldroles[n] else 0)+q/1000+rng.random()*.001 for n,q in choices])
 print('SOLVE',len(choices),len(rows),flush=True);tic=time.monotonic();ans=milp(cost,integrality=np.ones(len(choices)),bounds=Bounds(0,1),constraints=LinearConstraint(A.tocsc(),lo,hi),options={'time_limit':a.seconds});summary.update(solver=ans.message,seconds=time.monotonic()-tic,variables=len(choices),constraints=len(rows))
 if ans.x is None:summary['status']='NO_ALLOCATION';(a.output/'result.json').write_text(json.dumps(summary,indent=2));print(json.dumps(summary));return
 mapped={n:q for(n,q),x in zip(choices,ans.x)if x>.5};qnodes=defaultdict(list)
 for n,q in mapped.items():qnodes[q].append(n)
 N=dict(T)
 for q,ns in qnodes.items():
  for bit in(0,1):
   if(q,bit)in P:continue
   cs=[n[bit]for n in ns]
   if s.leaf(cs[0]):
    allowed=set(acts[cs[0],bit])
    for c in cs[1:]:allowed&=set(acts[c,bit])
    assert allowed
    direct=[act for act in allowed if act[:2]==(bit,1)]
    N[q,bit]=T[q,bit]if T[q,bit]in allowed else max(direct or allowed,key=lambda act:sum(acts[c,bit][act]for c in cs))
   else:assert len(set(cs))==1;N[q,bit]=(bit,1,mapped[cs[0]])
 # All helpers and engine stay literal; full prefixes must implement intended node map.
 assert all(T[k]==N[k]for k in P)
 reach={0};todo=[0]
 for q in todo:
  for bit in(0,1):
   z=N[q,bit][2]
   if z!=254 and z not in reach:reach.add(z);todo.append(z)
 N={k:v for k,v in N.items()if k[0]in reach};fail=[]
 for p,n in paths(new):
  tape={-1:1,**{i:int(v)for i,v in enumerate(p)}};before=dict(tape);h=0;q=84
  for step in range(10000):
   if h==len(p):break
   if h not in tape or(q,tape[h])not in N:break
   w,d,q=N[q,tape[h]];tape[h]=w;h+=d
  if h!=len(p)or tape!=before or not(q==mapped[n]or(n==aliasnode and q==108 and ('1'+p+'1').endswith('101'))):fail.append({'path':p,'expected':mapped[n],'actual':q,'head':h,'tape_changed':tape!=before})
 summary.update(status='PREFIX_PASS'if not fail else'PREFIX_FAIL',states=len(N)//2,failures=fail,changed_rows=[list(k)+list(N[k])for k in N if N[k]!=T[k]],mapping=[{'path':occ[n][0],'q':q}for n,q in mapped.items()]);(a.output/'machine.tm').write_bytes(b.table_bytes(N));(a.output/'result.json').write_text(json.dumps(summary,indent=2));print(json.dumps({k:v for k,v in summary.items()if k not in('domains','mapping','failures','changed_rows')},indent=2),flush=True)
if __name__=='__main__':main()
