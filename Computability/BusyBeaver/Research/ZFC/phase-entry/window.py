#!/usr/bin/env python3
"""Literal finite-window effects; arbitrary exterior preservation by trace locality."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import hashlib,json
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repo',type=Path,required=True)
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args()
if not __debug__:parser.error('Keep assertions enabled')
ROOT=args.repo.resolve();OUT=args.output.resolve()
if OUT==ROOT or ROOT in OUT.parents:parser.error('External scratch output required')
OUT.mkdir(parents=True,exist_ok=True)
BASE=ROOT/'Computability/BusyBeaver/Research/ZFC';sys.path.insert(0,str(BASE))
import candidate252_independent_audit as A
raw=(BASE/'candidate-permutation252/zfc_permutation252_old.tm').read_bytes()
assert hashlib.sha256(raw).hexdigest()==A.EXPECTED_SHA
original=A.read_table(raw)
records=[]
for action,steps in [((1,'L',229),36),((1,'R',252),34),((1,'R',77),6)]:
 table={k:v for k,v in original.items() if k[0]!=204};table[172,1]=action
 state,head,ones=96,0,{-1}|set(range(10));initial=set(ones);trace=[]
 for t in range(steps):
  assert state!=254
  read=int(head in ones);w,d,q=table[state,read]
  trace.append(dict(t=t,q=state,head=head,read=read,write=w,direction=d,next=q))
  if w:ones.add(head)
  else:ones.discard(head)
  head+=1 if d=='R' else -1;state=q
 scanned=[x['head'] for x in trace];lo,hi=min(scanned),max(scanned)
 if action[2]!=77:
  assert (state,head,ones)==(96,0,initial-{6})
  assert (lo,hi)==(-11,6)
 else:assert state==254
 records.append(dict(incoming_action=list(action),steps=steps,scan_window=[lo,hi],
    required_initial_ones_in_window=sorted(x for x in initial if lo<=x<=hi),
    final_state=state,final_head=head,changed_cells=sorted(initial^ones),
    initial_whole_ones=sorted(initial),final_whole_ones=sorted(ones),trace=trace))
r={'status':'PASS finite deterministic trace certificates','baseline_sha256':A.EXPECTED_SHA,
   'scope':'Each trace lifts by literal-step induction to every exterior completion of its stated finite input window. No register/Box oracle, source reachability, full mutant simulation or PA theorem is supplied.',
   'same_window_effect_first_two':all(records[0][k]==records[1][k] for k in ['scan_window','required_initial_ones_in_window','final_state','final_head','changed_cells','final_whole_ones']),
   'records':records,'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
assert r['same_window_effect_first_two']
(OUT/'window-results.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:v for k,v in r.items() if k!='records'},indent=2))
