#!/usr/bin/env python3
"""Search context-dependent leaf entries after a K219 source allocation.

Representative literal-PC proofs guide repair. Final acceptance requires the
full seeded runtime verifier on every actual source occurrence.
"""
from pathlib import Path
from collections import defaultdict
import argparse,json,sys,time
from primitive_probe import Probe,ROOT
sys.path.insert(0,str(ROOT/'source_work'));import rotation_search as r
from hardware_objective219 import model

def repair(T,tree):
 p=ROOT/'baseline219/K219_Construction_2026-10-20/machine';oldT=r.b.read_table((p/'k219.native.tm').read_bytes())
 old=r.normalise(r.s.tree(json.loads((p/'sites219.json').read_text())))
 _,meta=model(oldT,old,json.loads((ROOT/'source218/frozen_engine_rows219.json').read_text())['rows'])
 protected=meta['protected'];groups,paths,ns=r.mapping(T,tree);pathq={p:q for q,ps in paths.items()for p in ps}
 cases=defaultdict(list)
 for pc,op,arg in r.s.sites(tree):cases[pathq[pc[:-1]],int(pc[-1])].append((pc,op,arg))
 actions=defaultdict(set)
 for q,nodes in meta['groups'].items():
  for n in nodes:
   for bit,ch in enumerate(n):
    if r.s.leaf(ch):actions[ch,bit].add(oldT[q,bit])
 for bit in(0,1):
  for q in(4,40,27,162,103,119,302):actions[('CB',1),bit].add((0,-1,q))
  for q in(16,10,31):actions[('CC',2),bit].add((0,-1,q));actions[('CC',2),bit].add((1,-1,q))
  for q in(42,73,138):
   for w in(0,1):actions[('CC',3),bit].add((w,-1,q))
  for q in(83,160,161):
   for w in(0,1):actions[('CC',4),bit].add((w,-1,q))
 for((op,arg),bit),acts in list(actions.items()):
  if op in('CI','CD'):
   for w,d,q in acts:
    if d==1:actions[(op,arg),1-bit].add((1-bit,d,q))
 for arg,q in[(1,41),(3,17),(4,144),(5,45),(6,21)]:actions[('CD',arg),1].add((1,1,q))
 N=dict(T);changes=[];checked=0;start=time.monotonic()
 for round_index in range(2):
  changes_before=len(changes);probe=Probe(N);bad=[]
  for i,(key,allcases)in enumerate(cases.items()):
   seen=set();reps=[]
   for pc,op,arg in allcases:
    sig=(pc[-10:],op,arg)
    if sig not in seen:seen.add(sig);reps.append((pc,op,arg))
   choices=set.intersection(*(actions[(op,arg),key[1]]for pc,op,arg in reps));ordered=[N[key]]+sorted(choices-{N[key]});accepted=None
   for act in ordered:
    if key in protected and act!=T[key]:continue
    checked+=1
    if all(probe.test(pc,op,arg,act)for pc,op,arg in reps):accepted=act;break
   if accepted is None:bad.append(dict(row=key,prior=N[key],sites=reps,choices=ordered,protected=key in protected))
   elif accepted!=N[key]:
    changes.append(dict(row=key,old=N[key],new=accepted,round=round_index,sites=len(allcases)));N[key]=accepted;probe=Probe(N)
   if i%20==0:print('ROWS',i,'of',len(cases),'round',round_index,'changes',len(changes),'failures',len(bad),'seconds',round(time.monotonic()-start,1),flush=True)
  if len(changes)==changes_before:break
 return N,dict(status='LEAF_PROBES_PASS'if not bad else'UNREPAIRED_LEAVES',changes=changes,failures=bad,probed_actions=checked,seconds=time.monotonic()-start)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('directory',type=Path);ap.add_argument('--output',type=Path);a=ap.parse_args();out=a.output or a.directory/'leaf_repaired';out.mkdir(exist_ok=True,parents=True)
 T=r.b.read_table((a.directory/'candidate.tm').read_bytes());tree=r.normalise(r.s.tree(json.loads((a.directory/'sites.json').read_text())))
 N,receipt=repair(T,tree);(out/'candidate.tm').write_bytes(r.b.table_bytes(N));(out/'sites.json').write_bytes(r.s.compact(r.s.sites(tree)))
 (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2),flush=True)
if __name__=='__main__':main()
