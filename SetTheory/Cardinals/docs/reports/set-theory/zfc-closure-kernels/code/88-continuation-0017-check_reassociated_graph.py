#!/usr/bin/env python3
"""Independent exact occurrence-CFG comparison of two acyclic source DAGs."""
from pathlib import Path
import argparse,collections,hashlib,json
from independent_cfg import build_cfg

ap=argparse.ArgumentParser()
ap.add_argument("reference",type=Path)
ap.add_argument("candidate",type=Path)
ap.add_argument("--output",type=Path,required=True)
ap.add_argument("--operational-controls",action="store_true",
                help="Permit changed CB/CC operands only when all resolved successors agree.")
args=ap.parse_args()

def parse_graph(path):
    data=json.loads(path.read_text())
    entries={int(k):tuple(v) for k,v in data["entries"].items()}
    rows=[];leaves=[];seen=set()
    def expand(n,p,anc):
        assert n in entries and n not in anc
        seen.add(n);e=entries[n]
        if e[0]=="N":
            assert len(e)==3
            i=len(rows);rows.append(None)
            rows[i]=(expand(e[1],p+"0",anc+(n,)),expand(e[2],p+"1",anc+(n,)))
            return "CN",i
        assert len(e)==2
        op,r=e
        assert op in ("CI","CD","CB","CC","CH")
        if op in ("CI","CD"):assert type(r) is int and 0<=r<9
        elif op in ("CB","CC"):assert type(r) is int and r>0
        else:assert r is None
        leaves.append((p,op,r));return e
    assert expand(data["root"],"",())==("CN",0)
    assert seen==set(entries)
    assert len(rows)==6459 and len(leaves)==6460
    succ,initial=build_cfg(rows,leaves)
    return entries,rows,leaves,succ,initial

E0,R0,L0,S0,I0=parse_graph(args.reference)
E1,R1,L1,S1,I1=parse_graph(args.candidate)
exact_labels=[e[1:] for e in L0]==[e[1:] for e in L1]
def operational(e):
    _,op,r=e
    return ("SKIP",None) if op in ("CB","CC") else (op,r)
if args.operational_controls:
    assert list(map(operational,L0))==list(map(operational,L1))
else:assert exact_labels
assert S0==S1 and I0==I1
changed_controls=[{"occurrence":i,"reference":a[1:],"candidate":b[1:]}
                  for i,(a,b) in enumerate(zip(L0,L1)) if a[1:]!=b[1:]]
assert all(c["reference"][0] in ("CB","CC") and c["candidate"][0] in ("CB","CC")
           for c in changed_controls)
bad=[(i,p,r) for i,(p,op,r) in enumerate(L1) if op=="CD" and p.endswith("0"*7)]
zero_run=max(len(s) for p,_,_ in L1 for s in p.split("1"))
record={
    "status":"PASS",
    "reference":str(args.reference),"candidate":str(args.candidate),
    "reference_sha256":hashlib.sha256(args.reference.read_bytes()).hexdigest(),
    "candidate_sha256":hashlib.sha256(args.candidate.read_bytes()).hexdigest(),
    "all_entries_reachable_in_both_graphs":True,
    "all_instruction_kinds_and_operands_match_by_occurrence":exact_labels,
    "all_operational_labels_match_by_occurrence":True,
    "operational_control_mode":args.operational_controls,
    "changed_control_operands":len(changed_controls),
    "control_change_histogram":dict(collections.Counter(str(c["reference"])+" -> "+str(c["candidate"]) for c in changed_controls)),
    "control_changes":changed_controls,
    "all_guarded_successors_match_by_occurrence":True,
    "initial_control_matches":True,
    "source_primitive_steps_and_final_registers_preserved":True,
    "candidate_shared_pair_nodes":sum(e[0]=="N" for e in E1.values()),
    "candidate_terminal_entries":sum(e[0]!="N" for e in E1.values()),
    "leaves":len(L1),"guarded_edges":sum(map(len,S1)),
    "guarded_cases":sum(2 if op=="CD" else 1 for _,op,_ in L1),
    "maximum_depth":max(len(p) for p,_,_ in L1),"maximum_zero_run":zero_run,
    "decrement_leaves_ending_seven_zeros":len(bad),"bad_leaves":bad,
    "changed_leaf_paths":sum(a[0]!=b[0] for a,b in zip(L0,L1)),
    "method":"Independent DAG parsers and consumed-path control arithmetic; no optimizer or delivered checker imports.",
    "scope":"Exact operational one-instruction source bisimulation to the reference graph. Changed control operands are admitted only by explicit flag and exact resolved-successor equality. The reference requires its own calibration/source-equivalence proof; binary runtime is separate."
}
args.output.write_text(json.dumps(record,indent=2)+"\n")
print(json.dumps({k:v for k,v in record.items() if k not in ("bad_leaves","control_changes")},indent=2))
