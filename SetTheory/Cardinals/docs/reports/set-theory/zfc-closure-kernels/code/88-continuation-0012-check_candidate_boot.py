#!/usr/bin/env python3
"""Independent dense blank-prefix replay for an old-label Context246 derivative."""
from pathlib import Path
import argparse,hashlib,json
ROOT=Path(__file__).resolve().parents[2]
ap=argparse.ArgumentParser();ap.add_argument("table",type=Path);ap.add_argument("--output",type=Path,required=True)
ap.add_argument("--allow-changed-prefix-rows",action="store_true")
ap.add_argument("--baseline",type=Path,default=ROOT/"vendor/context246/machine/zfc_prefix246_old.tm")
args=ap.parse_args()
table={}
for n,line in enumerate(args.table.read_text().splitlines(),1):
    if not line.strip() or line.startswith("#"):continue
    q,b,w,d,t=line.split()
    q,b,w,t=map(int,(q,b,w,t))
    assert b in (0,1) and w in (0,1) and d in ("L","R")
    assert (q,b) not in table
    table[q,b]=w,(1 if d=="R" else -1),t
states={q for q,b in table}
assert len(states)==246 and len(table)==492 and 95 in states
assert all((q,b) in table for q in states for b in (0,1))
assert {t for _,_,t in table.values()}-states=={254}
assert sum(t==254 for _,_,t in table.values())==1

offset=1024;tape=bytearray(4096);head=offset;state=95;minimum=maximum=0
used=set()
for step in range(410735):
    assert state in states and 0<=head<len(tape)
    key=state,tape[head];used.add(key);w,d,state=table[key]
    tape[head]=w;head+=d
    minimum=min(minimum,head-offset);maximum=max(maximum,head-offset)
ones={i-offset for i,b in enumerate(tape) if b}
expected={-6,176};pos=177
for value in [0,0,0,3,0,0,3,0,0]+[1]*167:
    expected.update(range(pos+1,pos+value+2));pos+=value+2
assert pos==702 and len(expected)==351
assert state==96 and head-offset==-5 and ones==expected

baseline={}
for line in args.baseline.read_text().splitlines():
    if not line.strip() or line.startswith("#"):continue
    q,b,w,d,t=line.split();baseline[int(q),int(b)]=(int(w),1 if d=="R" else -1,int(t))
changed_used_rows=[{"state":k[0],"read":k[1],"baseline":baseline.get(k),"candidate":table[k]}
                  for k in sorted(used) if baseline.get(k)!=table[k]]
assert not changed_used_rows or args.allow_changed_prefix_rows
record={"status":"PASS","working_states":len(states),"transitions":len(table),"unique_halting_edge":True,
        "table":str(args.table),"table_sha256":hashlib.sha256(args.table.read_bytes()).hexdigest(),
        "baseline_sha256":hashlib.sha256(args.baseline.read_bytes()).hexdigest(),
        "blank_steps":410735,"head":head-offset,"state":state,"ones":len(ones),
        "dense_tape_window":[-offset,len(tape)-offset-1],"head_range":[minimum,maximum],
        "complete_tape_matches_explicit_frame":True,"header_distance":181,
        "physical_primary":[0,0,0,3,0,0,3,0,0],"logical_primary":[3,0,0,0,3,0,0,0,0],
        "spare_count":167,"all_spares_value":1,"final_support":sorted(ones),
        "all_used_prefix_rows_unchanged_from_baseline":not changed_used_rows,
        "changed_rows_used_during_prefix":changed_used_rows,
        "method":"Own parser and dense bytearray interpreter, explicit frame generated independently.",
        "scope":"Exact finite bootstrap and table shape; no global nonhalting conclusion."}
args.output.write_text(json.dumps(record,indent=2)+"\n")
print(json.dumps({k:v for k,v in record.items() if k!="final_support"},indent=2))

