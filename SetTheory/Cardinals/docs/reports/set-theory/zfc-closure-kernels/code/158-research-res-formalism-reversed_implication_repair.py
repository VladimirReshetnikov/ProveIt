#!/usr/bin/env python3
"""Bounded randomized grammar reconstruction for reversed implication source."""
from pathlib import Path
import sys,json,random,time,math
HERE=Path(__file__).resolve().parent
# Import the definitions without running the fixed-scaffold experiment.
exec((HERE/'reversed_implication_price.py').read_text().split('revroot=rebuild')[0])
mprev=(((('CD',4),(('CI',7),(('CI',6),('CC',3)))),(('CD',7),(('CI',4),('CC',2)))),q(106))
word=sum((emit(t,True)for t in asts),[])
# Intern base grammar, including closed MP microcode.
bnodes=[];bid={}
def intern(t):
 key=t if s.leaf(t)else(intern(t[0]),intern(t[1]))
 if key not in bid:bid[key]=len(bnodes);bnodes.append(key)
 return bid[key]
intern(root);intern(mprev);mi={k:intern(t)for k,t in macros.items()};initial=[mi[x]for x in word]
def reparse(rng,trial):
 ns=bnodes.copy();idx=bid.copy();seq=initial.copy()
 dep=[0]*len(ns)
 for i,z in enumerate(ns):
  if isinstance(z[0],int):dep[i]=1+max(dep[z[0]],dep[z[1]])
 while len(seq)>1:
  pairs={}
  for i in range(len(seq)-1):
   p=(seq[i],seq[i+1]);pairs.setdefault(p,[]).append(i)
  choices=[]
  for p,at in pairs.items():
   prev=-2;count=0
   for a in at:
    if a>prev+1:count+=1;prev=a
   score=count-(0 if p in idx else 1)
   depth=1+max(dep[p[0]],dep[p[1]])
   noise=rng.random()*(0.001 if trial==0 else(0.5 if trial%3==0 else 1.3))
   choices.append((score+noise-0.01*depth,p))
  _,p=max(choices)
  if p not in idx:idx[p]=len(ns);ns.append(p);dep.append(1+max(dep[p[0]],dep[p[1]]))
  v=idx[p];ans=[];i=0
  while i<len(seq):
   if i+1<len(seq)and(seq[i],seq[i+1])==p:ans.append(v);i+=2
   else:ans.append(seq[i]);i+=1
  seq=ans
 def dec(i):
  t=ns[i];return t if not isinstance(t[0],int)else(dec(t[0]),dec(t[1]))
 return dec(seq[0])

def patch(t):
 t=m.splice(s,root,135,4563,t)
 return m.splice(s,t,4652,4705,mprev)
out=HERE/'reversed-implication-repair';out.mkdir(exist_ok=True);rng=random.Random(217);start=time.monotonic();best=999;best6=999;trial=0;records=[]
while time.monotonic()-start<75:
 small=reparse(rng,trial);t=patch(small);met=s.metrics(t)
 if met['dag_nodes']<best or(met['maximum_zero_run']<=6 and met['dag_nodes']<best6):
  best=min(best,met['dag_nodes'])
  if met['maximum_zero_run']<=6:best6=min(best6,met['dag_nodes'])
  rr=s.sites(t);assert s.graph_intervals(rr)==s.graph_arithmetic(rr)[0];d=out/f'candidate{trial:06d}';d.mkdir(exist_ok=True);(d/'sites.json').write_bytes(s.compact(rr));info=dict(trial=trial,metrics=met,seconds=time.monotonic()-start);(d/'result.json').write_text(json.dumps(info,indent=2));records.append(info);print('BEST',info,flush=True)
 trial+=1
(out/'result.json').write_text(json.dumps(dict(trials=trial,best=best,best6=best6,seconds=time.monotonic()-start,records=records),indent=2));print('DONE',trial,best,best6,flush=True)
