"""Check new scalar operations, base-three constructors, and literal tables.

Finite operational checks are not an unbounded compiler simulation. The
source-level register interpreter and normalizer are attributed vendored
ProveIt tools; literal action correspondence is also checked below.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib
import itertools
import json
from pathlib import Path
import sys


def pair(a, b):
    return (a+b)*(a+b+1)//2+b


def scalar_and_constructor_checks(backend, rwd, execute_helper, nodes, names):
    builder = rwd.builder_from_dag(backend, nodes, names)
    builder.sequence_lookup = {s.seq: i for i, s in enumerate(builder.sequences)}
    roots = {}
    for macro, register in ((166,4), (121,5), (168,3)):
        for offset in (1,2,3):
            roots[macro,register,offset] = builder.add_sequence([macro]+["3.topwff.inc"]*offset)
    builder.reduce_to_cons()
    builder.name_sequences()
    scalar = 0
    for (macro, register, offset), root in roots.items():
        for selected, old, tail in itertools.product(range(5), range(3), (0,1,3)):
            values = [19,old,tail,2,3,4,0,0,23]
            values[register] = selected
            expected = list(values)
            expected[1] = selected+offset
            expected[2] = pair(old,tail)
            if execute_helper(builder,root,values) != ("normal",) or values != expected:
                raise AssertionError((macro,register,offset,selected,old,tail))
            scalar += 1
    builder.sequences[118].seq = (157,builder.sequences[118].seq[1])
    constructors = 0
    for root,tag in ((119,0),(181,1),(180,2)):
        for a,b,rest in itertools.product(range(4),range(4),(0,1,7)):
            values = [11,b,pair(a,rest),0,17,19,0,0,23]
            expected = [11,3*pair(a,b)+tag,rest,0,17,19,0,0,23]
            if execute_helper(builder,root,values) != ("normal",) or values != expected:
                raise AssertionError((root,tag,a,b,rest,values,expected))
            constructors += 1
    return {"scalar_push_offset_cases":scalar,"base3_constructor_cases":constructors}


def parse_rows(data):
    rows, start = {}, None
    for line in data.decode().splitlines():
        if line.startswith("#! start "):
            if start is not None:
                raise ValueError("duplicate start")
            start=line.split()[2]
        elif line and not line.startswith("#"):
            q,b,w,d,t=line.split()
            if b not in ("0","1") or w not in ("0","1") or d not in ("L","R"):
                raise ValueError("bad action")
            if (q,b) in rows:
                raise ValueError("duplicate row")
            rows[q,b]=w,d,t
    return start,rows


def correspondence(named, numeric, labels):
    oldstart,old=parse_rows(named)
    newstart,new=parse_rows(numeric)
    n=len(labels)-1
    if sorted(labels.values()) != list(range(n+1)) or labels["halt"] != n:
        raise AssertionError("invalid label permutation")
    if newstart != "0" or labels[oldstart] != 0:
        raise AssertionError("start changed")
    if set(new) != {(str(q),str(b)) for q in range(n) for b in (0,1)}:
        raise AssertionError("numeric table is not total")
    for (q,b),(w,d,t) in old.items():
        if new[str(labels[q]),b] != (w,d,str(labels[t])):
            raise AssertionError("an original action changed")
    if len(new) != len(old)+1 or ("1.inc","1") in old:
        raise AssertionError("unexpected totalization count")
    if new[str(labels["1.inc"]),"1"] != ("1","R",str(n)):
        raise AssertionError("wrong missing-row totalization")
    return {"working_states":n,"independently_compared_original_rows":len(old),
            "total_rows":len(new),"added_rows":1,"start":0,"halt":n}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    here=Path(__file__).resolve().parent
    parser.add_argument("--input",type=Path,default=here/"measurement")
    parser.add_argument("--output",type=Path,default=here/"audit")
    args=parser.parse_args()
    source=here/"vendor/proveit/Computability/BusyBeaver/Research/ZFC"
    backend_path=here/"vendor/proveit/lib/jeff-busy-beaver-zfc254/ZF/generator"
    sys.path.insert(0,str(source))
    sys.path.insert(0,str(backend_path))
    import recover_wade_dag as rwd
    from pairing_backend_experiment import execute_helper
    from audit_raw_candidate import normalize_named
    backend=importlib.import_module("TMBuilder")
    nodes,names=rwd.parse_dag(rwd.git_bytes(None,"ZF/m254/coq/prog/Dag254.v").decode())
    args.output.mkdir(parents=True,exist_ok=True)
    evidence={"status":"finite operational and exact literal checks only",
        "helper_checks":scalar_and_constructor_checks(backend,rwd,execute_helper,nodes,names),
        "tables":{},"unbounded_compiler_simulation":False}
    measurements=json.loads((args.input/"proxy_measurements.json").read_text())
    for key,record in measurements["variants"].items():
        named=(args.input/(key+".named.tm")).read_bytes()
        if hashlib.sha256(named).hexdigest()!=record["best"]["named_table_sha256"]:
            raise AssertionError("named source differs from frozen measurement")
        numeric,labels,normal=normalize_named(named)
        checked=correspondence(named,numeric,labels)
        if checked["working_states"]!=record["best"]["working_states"]:
            raise AssertionError("state count differs")
        (args.output/(key+".tm")).write_bytes(numeric)
        (args.output/(key+".labels.json")).write_text(json.dumps(labels,indent=2)+"\n")
        evidence["tables"][key]={"independent":checked,"normalization":normal}
    (args.output/"proxy_artifact_audit.json").write_text(json.dumps(evidence,indent=2)+"\n")
    print(json.dumps({"helper_checks":evidence["helper_checks"],
                      "literal_tables":len(evidence["tables"])},indent=2))


if __name__=="__main__":
    main()
