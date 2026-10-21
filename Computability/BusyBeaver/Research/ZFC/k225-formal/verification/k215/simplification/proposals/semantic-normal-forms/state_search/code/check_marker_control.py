#!/usr/bin/env python3
"""Positive control: reconstruct the known state-neutral52/176 marker fold."""
from pathlib import Path
from collections import defaultdict
import json,argparse,hashlib
from context_fold_search import read_table,backward_impossible
from context_fold_search_v2 import prove
ap=argparse.ArgumentParser();ap.add_argument('table',type=Path);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
t,start,states=read_table(args.table)
assert hashlib.sha256(args.table.read_bytes()).hexdigest()=='9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2'
pred=defaultdict(list)
for(q,a),(w,d,n)in t.items():pred[n].append((q,a,w,d))
assert backward_impossible(pred,start,52,{0:0,-1:0},12,10000)
assert backward_impossible(pred,start,176,{0:0,-1:1},12,10000)
assert t[52,1]==t[176,1]
u=dict(t);fresh=999
assert fresh not in states
u[fresh,0]=(0,1,185);u[fresh,1]=(1,1,129)
co={(52,0):{0:0,-1:1},(176,0):{0:0,-1:0}}
checks=[]
for origin in(52,176):
 r,n,d=prove(u,52,176,0,co,fresh,0,-1,origin,96,14,4096)
 assert(r,d)==('PASS',3)
 checks.append({'origin':origin,'status':r,'symbolic_nodes':n,'duration':d})
result={'status':'PASS','scope':'Known215-state state-neutral52/176 marker fold; one old state deleted and one new selector added. This is an independent positive control of the bounded symbolic provider checker, not a214 result.','checks':checks,'working_states_after_fold':len(states)-1+1}
args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
