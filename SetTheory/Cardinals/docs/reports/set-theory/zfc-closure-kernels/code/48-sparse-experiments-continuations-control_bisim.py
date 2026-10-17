#!/usr/bin/env python3
"""Finite, strong and jump-contracted control bisimulation for Prog254."""
from pathlib import Path
from collections import Counter
import hashlib, json
from permutation252_phase_analysis import program_graph

BASE=Path(__file__).resolve().parent

def build():
 sites,cases,targets,first=program_graph((BASE/'Prog254.v').read_bytes())
 bysite={i:[] for i in range(len(sites))}
 for i,(site,*_) in enumerate(cases):bysite[site].append((i,targets[i]))
 # Control-only nodes have one successor independent of the register file.
 closure={};rank={}
 def close(i):
  trail=[];seen=set();q=i
  while q not in closure and sites[q][1] in ('CB','CC'):
   if q in seen:
    for p in trail:closure[p]=-1;rank[p]=0
    return -1
   seen.add(q);trail.append(q);q=bysite[q][0][1]
   assert q is not None
  if q not in closure:closure[q]=q;rank[q]=0
  for p in reversed(trail):closure[p]=closure[q];rank[p]=rank[q]+1;q=p
  return closure[i]
 for i in range(len(sites)):close(i)
 core=sorted({closure[i] for i in range(len(sites))})
 assert -1 not in core
 part={i:0 for i in core};counts=[]
 while True:
  labels={};new={}
  for i in core:
   _,op,r=sites[i]
   sig=(op,r,tuple(None if t is None else part[closure[t]]for c,t in bysite[i]))
   new[i]=labels.setdefault(sig,len(labels))
  counts.append(len(labels))
  if new==part:break
  part=new
 classes={i:part[closure[i]] for i in range(len(sites))}
 return sites,cases,targets,first,bysite,closure,rank,classes,counts

if __name__=='__main__':
 sites,cases,targets,first,bysite,closure,rank,classes,counts=build()
 groups={}
 for i,c in classes.items():groups.setdefault(c,[]).append(i)
 print(json.dumps({'sites':len(sites),'core':len(set(closure.values())),'class_counts':counts,
  'largest_classes':Counter({k:len(v)for k,v in groups.items()}).most_common(20),'max_jump_rank':max(rank.values()),'jump_rank_counts':dict(Counter(rank.values()))},indent=2))
