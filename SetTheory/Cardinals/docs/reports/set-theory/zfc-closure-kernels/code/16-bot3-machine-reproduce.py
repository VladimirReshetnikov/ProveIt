"""Replay three fixed compiler measurements and independently audit normalization.

Run with Python 3.10+; no dependencies, network, Coq, Lean, or full search.
The sibling proveit_snapshot is read only; output is a separate directory.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib
import json
from pathlib import Path
import re
import sys

import old_rho6_grammar_search as grammar
import bottom3_measurement as bottom3
import quantifier_obstruction


def check_correspondence(named, numeric, labels):
    """Independently parse both files and compare every action under relabelling."""
    old,new={},{}
    starts=[]
    for raw in named.decode().splitlines():
        if raw.startswith("#! start "):
            starts.append(raw.removeprefix("#! start "))
        elif raw and not raw.startswith("#"):
            match=re.fullmatch(r"(\S+) ([01]) ([01]) ([LR]) (\S+)",raw)
            if not match:
                raise ValueError("independent named parser rejects row")
            q,b,w,d,t=match.groups()
            key=(q,int(b))
            if key in old:
                raise ValueError("duplicate named row")
            old[key]=(int(w),d,t)
    newstart=[]
    for raw in numeric.decode().splitlines():
        if raw.startswith("#! start "):
            newstart.append(int(raw.removeprefix("#! start ")))
        elif raw and not raw.startswith("#"):
            match=re.fullmatch(r"(\d+) ([01]) ([01]) ([LR]) (\d+)",raw)
            if not match:
                raise ValueError("independent numeric parser rejects row")
            q,b,w,d,t=match.groups()
            key=(int(q),int(b))
            if key in new:
                raise ValueError("duplicate numeric row")
            new[key]=(int(w),d,int(t))
    n=len(labels)-1
    if sorted(labels.values())!=list(range(n+1)) or labels["halt"]!=n:
        raise ValueError("labels are not a bijection with halt last")
    if len(starts)!=1 or newstart!=[labels[starts[0]]] or newstart!=[0]:
        raise ValueError("start states disagree")
    if set(new)!=set((q,b) for q in range(n) for b in (0,1)):
        raise ValueError("numeric table is not exactly total on working states")
    if ("1.inc",1) in old or len(new)!=len(old)+1:
        raise ValueError("normalization did not add exactly the expected row")
    for (q,b),(w,d,t) in old.items():
        if new[labels[q],b]!=(w,d,labels[t]):
            raise ValueError("an original transition changed during normalization")
    if new[labels["1.inc"],1]!=(1,"R",n):
        raise ValueError("normalized missing row is incorrect")
    reachable={0}
    pending=[0]
    while pending:
        q=pending.pop()
        for bit in (0,1):
            target=new[q,bit][2]
            if target<n and target not in reachable:
                reachable.add(target)
                pending.append(target)
    return {"independently_compared_original_rows":len(old),
            "added_tape_preserving_halt_rows":1,"total_numeric_rows":len(new),
            "working_states":n,"graph_reachable_working_states":len(reachable),
            "exact_action_correspondence":True}


def main():
    if not __debug__:
        raise RuntimeError("run without -O")
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output",type=Path)
    args=ap.parse_args()
    root=Path(__file__).resolve().parent
    repo=root/"proveit_snapshot"
    out=(args.output or root/"reproduced").resolve()
    if out==repo or repo in out.parents:
        ap.error("output must be outside the source snapshot")
    pins=json.loads((root/"snapshot-sha256.json").read_text())
    for relative,pin in pins.items():
        if hashlib.sha256((repo/relative).read_bytes()).hexdigest()!=pin:
            raise ValueError("source hash mismatch: "+relative)
    out.mkdir(parents=True,exist_ok=True)
    source=repo/"Computability/BusyBeaver/Research/ZFC"
    sys.path.insert(0,str(source))
    import recover_wade_dag as rwd
    import theory_backend_experiment as tbe
    import psc_backend_experiment as psc
    from pairing_backend_experiment import execute_helper
    from audit_raw_candidate import normalize_named
    for name in ("TMBuilder.py","tm.py","tmdb.py","LICENSE.wade"):
        (out/name).write_bytes(rwd.git_bytes(None,"ZF/generator/"+name))
    sys.path.insert(0,str(out))
    backend=importlib.import_module("TMBuilder")
    nodes,names=rwd.parse_dag(rwd.git_bytes(None,"ZF/m254/coq/prog/Dag254.v").decode())
    tbe.old_contract(nodes)
    closed=grammar.closed_macro_checks(nodes,tbe.MACROS)
    cgv=tbe.equality_free_rows(dual=False,order=(1,7,5,3),components=("V","C","G"),grouping=1)
    spec,_=tbe.published_spec()
    rows=spec["ax_rows"]("a","h","b","c","u")
    vr=tbe.Imp(tbe.Rel("a","b"),tbe.All("c",tbe.Rel("a","b")))
    psc_word=[166,121,180,176]+[m for i in (3,1,7,5) for m in psc.emit(rows[i])]
    psc_word+=psc.emit(psc.psc_template("k"))+psc.emit(vr)+tbe.TAIL
    cases=[
        ("cgv-relative-bottom-250",cgv,7,False,250,
         "f7e07030ddad354cca426cedf730fc212b444e542223ee65ac64635fae0554ab"),
        ("cgv-genuine-bottom3-251",cgv,7,True,251,
         "77ab5089340cf2722dccdc44b8da91df232d592873cf35acd8d80c9efc387495"),
        ("psc-genuine-bottom3-252",psc_word,93,True,252,
         "1b804bc8c456888f45338cbace5a5a927dd8ab8addf6345a19db65992fd04c58"),
    ]
    results={}
    for name,word,seed,genuine,count,pin in cases:
        builder,g=grammar.build(backend,nodes,names,word,seed,4,rwd,tbe)
        if genuine:
            bottom3.set_bottom3(builder)
        record=grammar.record(builder,out/(name+".named.tm"))
        if record["working_states"]!=count or record["named_table_sha256"]!=pin:
            raise ValueError("fixed winner failed byte-for-byte replay: "+name)
        if genuine:
            record["constructor_contract_cases"]=bottom3.constructor_checks(builder,execute_helper)
        named=(out/(name+".named.tm")).read_bytes()
        numeric,labels,normal=normalize_named(named)
        correspondence=check_correspondence(named,numeric,labels)
        (out/(name+".tm")).write_bytes(numeric)
        (out/(name+".labels.json")).write_text(json.dumps(labels,indent=2,sort_keys=True)+"\n")
        results[name]={"seed":seed,"exponent":4,"grammar":g,"measurement":record,
                       "normalization":normal,"independent_correspondence":correspondence,
                       "macro_word_sha256":hashlib.sha256(json.dumps(word,separators=(",",":")).encode()).hexdigest()}
    evidence={"pinned_proveit_head":grammar.PINNED_HEAD,"upstream_commit":rwd.COMMIT,
              "verified_input_files":len(pins),"closed_macro_bounds":closed,
              "fixed_winners":results,"quantifier_obstruction":quantifier_obstruction.check(),
              "all_original_rho6":True,"first_order_calibration_proved":False,
              "compiler_simulation_proved":False,"ZFC_nonhalting_equivalence_proved":False,
              "new_ZFC_machine_state_bound_claimed":False}
    (out/"reproduction.json").write_text(json.dumps(evidence,indent=2,sort_keys=True)+"\n")
    print(json.dumps({name:{"states":r["measurement"]["working_states"],
                           "rows":r["normalization"]["transition_rows_after"],
                           "numeric_sha256":r["normalization"]["numeric_table_sha256"]}
                      for name,r in results.items()},indent=2),flush=True)


if __name__=="__main__":
    main()
