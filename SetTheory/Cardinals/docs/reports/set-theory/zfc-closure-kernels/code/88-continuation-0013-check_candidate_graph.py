#!/usr/bin/env python3
"""Independently parse and compare a transformed source DAG with literal Prog254."""
from pathlib import Path
import argparse,hashlib,json,collections
from independent_cfg import parse_source,build_cfg
ROOT=Path(__file__).resolve().parents[2]
ap=argparse.ArgumentParser();ap.add_argument("candidate",type=Path);ap.add_argument("--output",type=Path,required=True)
ap.add_argument("--source",type=Path,default=ROOT/"vendor/context246/sources/Prog254.v")
args=ap.parse_args()
original_rows,original_leaves=parse_source(args.source)
original_succ,_=build_cfg(original_rows,original_leaves)
data=json.loads(args.candidate.read_text())
entries={int(k):tuple(v) for k,v in data["entries"].items()}
rows=[];leaves=[];seen=set()
def expand(node,path,ancestors):
    assert node in entries and node not in ancestors
    seen.add(node);entry=entries[node]
    if entry[0]=="N":
        assert len(entry)==3
        index=len(rows);rows.append(None)
        left=expand(entry[1],path+"0",ancestors+(node,))
        right=expand(entry[2],path+"1",ancestors+(node,))
        rows[index]=(left,right)
        return "CN",index
    op,arg=entry
    assert op in ("CI","CD","CB","CC","CH")
    if op in ("CI","CD"):assert type(arg) is int and 0<=arg<9
    elif op in ("CB","CC"):assert type(arg) is int and arg>0
    else:assert arg is None
    leaves.append((path,op,arg))
    return op,arg
assert expand(data["root"],"",())==("CN",0)
assert seen==set(entries)
assert len(rows)==6459 and len(leaves)==6460
assert [e[1:] for e in leaves]==[e[1:] for e in original_leaves]
succ,initial=build_cfg(rows,leaves)
assert succ==original_succ and initial==0
bad=[(i,p,arg) for i,(p,op,arg) in enumerate(leaves) if op=="CD" and p.endswith("0"*7)]
numpairs=sum(e[0]=="N" for e in entries.values())
zero_run=max(len(run) for p,_,_ in leaves for run in p.split("1"))
record={"status":"PASS","candidate":str(args.candidate),"shared_pair_nodes":numpairs,
        "candidate_sha256":hashlib.sha256(args.candidate.read_bytes()).hexdigest(),
        "source_sha256":hashlib.sha256(args.source.read_bytes()).hexdigest(),
        "terminal_entries":len(entries)-numpairs,"all_entries_reachable":True,
        "all_instruction_kinds_and_operands_match_by_occurrence":True,
        "all_guarded_successors_match_by_occurrence":True,
        "literal_internal_nodes":len(rows),"leaves":len(leaves),"guarded_edges":sum(map(len,succ)),
        "guarded_cases":sum(2 if op=="CD" else 1 for _,op,_ in leaves),
        "maximum_depth":max(len(p) for p,_,_ in leaves),"maximum_zero_run":zero_run,
        "decrement_leaves_ending_seven_zeros":len(bad),"bad_leaves":bad,
        "changed_leaf_paths":sum(a[0]!=b[0] for a,b in zip(leaves,original_leaves)),
        "method":"Own literal/DAG parsers and RegisterPath arithmetic; no root/delivered checker imports.",
        "scope":"Exact source instruction bisimulation only; no binary state count inferred."}
args.output.write_text(json.dumps(record,indent=2)+"\n")
print(json.dumps({k:v for k,v in record.items() if k!="bad_leaves"},indent=2))

