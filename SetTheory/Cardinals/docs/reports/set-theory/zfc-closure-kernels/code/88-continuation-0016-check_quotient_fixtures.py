#!/usr/bin/env python3
"""Independent coverage and register-effect audit of the finite quotient fixtures."""
from pathlib import Path
import json, argparse
from independent_cfg import parse_source,build_cfg
ROOT=Path(__file__).resolve().parents[2]
ap=argparse.ArgumentParser()
ap.add_argument("--source",type=Path,default=ROOT/"vendor/context246/sources/Prog254.v")
ap.add_argument("--quotient",type=Path,default=ROOT/"experiments/audit_inputs/quotient.json")
ap.add_argument("--original-cases",type=Path,default=ROOT/"experiments/audit_inputs/cases_semantic.txt")
ap.add_argument("--prepared-cases",type=Path,default=ROOT/"experiments/audit_inputs/quotient_cases.txt")
ap.add_argument("--output",type=Path,default=ROOT/"results/audit/fixture_audit.json")
args=ap.parse_args()
rows,leaves=parse_source(args.source)
succ,_=build_cfg(rows,leaves);lookup={p:i for i,(p,_,_) in enumerate(leaves)}
def decode(bits):
    node=0;word="";depth=0
    while True:
        b=bits(depth);depth+=1;word+=str(b)
        op,arg=rows[node][b]
        if op!="CN":return lookup[word]
        node=arg
def registers(ones,header):
    p=header+1;result=[]
    for _ in range(9):
        assert p not in ones
        e=p+1
        while e in ones:e+=1
        assert e>=p+2
        result.append(e-p-2);p=e
    return result
physical_to_logical=(2,8,1,4,3,7,0,5,6)
logical_to_physical={r:i for i,r in enumerate(physical_to_logical)}
q=json.loads(args.quotient.read_text())
original=args.original_cases.read_text().splitlines()
prepared=args.prepared_cases.read_text().splitlines()
seen=set();nonhalt=0
assert len(original)==len(prepared)==8391
for case,(line,out) in enumerate(zip(original,prepared)):
    tokens=line.split();n=int(tokens[0]);ones={int(x) for x in tokens[1:n+1]}
    cursor=n+1
    targetstate=int(tokens[cursor]);head=int(tokens[cursor+1]);pc=tokens[cursor+2]
    targetregs=list(map(int,tokens[cursor+3:cursor+12]))
    leaf=decode(lambda d:int(d in ones))
    path,op,arg=leaves[leaf];vals=registers(ones,40)
    if op=="CD":guard=vals[logical_to_physical[arg]]>0
    else:guard=None
    assert (leaf,guard) not in seen,(case,leaf,guard)
    seen.add((leaf,guard))
    if op=="CH":
        assert targetstate==254
    else:
        assert targetstate==96
        nonhalt+=1;expected=vals[:]
        if op=="CI":expected[logical_to_physical[arg]]+=1
        if op=="CD" and guard:expected[logical_to_physical[arg]]-=1
        assert targetregs==expected,(case,targetregs,expected)
        actualpc="" if pc=="-" else pc
        nextleaf=decode(lambda d:int(actualpc[d]) if d<len(actualpc) else 0)
        wanted=succ[leaf][int(guard)] if op=="CD" else succ[leaf][0]
        assert nextleaf==wanted,(case,nextleaf,wanted)
        cls,rnk=map(int,out.split()[:2])
        assert cls==q["classes"][wanted] and rnk==q["rank"][wanted]
    assert " ".join(out.split()[2:])==line
wanted={(i,g) for i,(_,op,_) in enumerate(leaves)
        for g in ((False,True) if op=="CD" else (None,))}
assert seen==wanted
record={"status":"PASS","cases":len(original),"all_guarded_source_cases_covered_once":True,
        "nonhalting_cases":nonhalt,"halting_cases":len(original)-nonhalt,
        "independent_source_register_effects_match":True,
        "independent_source_successor_leaf_matches":True,
        "prepared_class_and_rank_bounds_match":True,
        "method":"Own parser, own path arithmetic, own unary-file decoding; no root/delivered checker imports.",
        "scope":"Finite fixture coverage and expectations; no universal binary simulation claim."}
args.output.write_text(json.dumps(record,indent=2)+"\n")
print(json.dumps(record,indent=2))

