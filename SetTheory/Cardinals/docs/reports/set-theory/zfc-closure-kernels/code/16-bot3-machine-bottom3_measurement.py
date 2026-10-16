"""Measure the genuine-Bottom ternary codec on old-rho6 source programs.

No claim of first-order completeness, consistency calibration, or compiler
verification is made.  This changes only Rel's tag offset, not logical rows.
The first lane is C/G/V; the second is the repository's incomplete PSC control.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import importlib
import json
from pathlib import Path
import sys

import old_rho6_grammar_search as grammar


def set_bottom3(builder):
    # Dag254:159=inc;inc,157=159;inc,156=157;inc.  Thus156 adds4.
    # The multiplier has already changed to x3 at loop118.  Both formula and
    # proof/stack pairing stay exactly as before; constant1 stays the target.
    if builder.sequences[181].seq != (119, "3.topwff.inc"):
        raise ValueError("unexpected membership constructor shape")
    builder.sequences[181].seq = (119, 156)
    builder.reduce_to_cons()
    builder.name_sequences()


def constructor_checks(builder, execute_helper):
    pair = lambda a,b: (a+b)*(a+b+1)//2+b
    cases = 0
    for a in range(5):
        for b in range(5):
            for rest in (0,1,5):
                for root, offset in ((119,0),(181,4),(180,2)):
                    values = [7,b,pair(a,rest),0,11,13,0,0,19]
                    expected = [7,3*pair(a,b)+offset,rest,0,11,13,0,0,19]
                    if execute_helper(builder,root,values) != ("normal",) or values != expected:
                        raise ValueError("ternary Bottom constructor contract failed")
                    cases += 1
    return cases


def main():
    if not __debug__:
        raise RuntimeError("run without -O")
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo",type=Path,required=True)
    ap.add_argument("--output",type=Path,required=True)
    ap.add_argument("--seeds",type=int,default=200)
    args = ap.parse_args()
    repo,out = args.repo.resolve(),args.output.resolve()
    if out == repo or repo in out.parents:
        ap.error("output must be outside source snapshot")
    out.mkdir(parents=True,exist_ok=True)
    source=repo/"Computability/BusyBeaver/Research/ZFC"
    sys.path.insert(0,str(source))
    import recover_wade_dag as rwd
    import theory_backend_experiment as tbe
    import psc_backend_experiment as psc
    from pairing_backend_experiment import execute_helper
    for name in ("TMBuilder.py","tm.py","tmdb.py","LICENSE.wade"):
        (out/name).write_bytes(rwd.git_bytes(None,"ZF/generator/"+name))
    sys.path.insert(0,str(out))
    backend=importlib.import_module("TMBuilder")
    nodes,names=rwd.parse_dag(rwd.git_bytes(None,"ZF/m254/coq/prog/Dag254.v").decode())
    tbe.old_contract(nodes)
    closed=grammar.closed_macro_checks(nodes,tbe.MACROS)
    programs={"CGV_original_rho6":tbe.equality_free_rows(dual=False,order=(1,7,5,3),
                                                       components=("V","C","G"),grouping=1)}
    spec,_=tbe.published_spec()
    rows=spec["ax_rows"]("a","h","b","c","u")
    vr=tbe.Imp(tbe.Rel("a","b"),tbe.All("c",tbe.Rel("a","b")))
    word=[166,121,180,176]+[m for i in (3,1,7,5) for m in psc.emit(rows[i])]
    word+=psc.emit(psc.psc_template("k"))+psc.emit(vr)+tbe.TAIL
    programs["PSC_original_rho6"]=word
    results={}
    for lane,program in programs.items():
        costs=Counter()
        best=None
        minimizers=[]
        control,_=grammar.build(backend,nodes,names,program,None,4,rwd,tbe)
        set_bottom3(control)
        control_record=grammar.record(control,out/(lane+"_control.tm"))
        for seed in range(args.seeds):
            builder,g=grammar.build(backend,nodes,names,program,seed,4,rwd,tbe)
            set_bottom3(builder)
            record=grammar.record(builder,None)
            cost=record["working_states"]
            costs[cost]+=1
            if best is None or cost<best["working_states"]:
                best=record|{"seed":seed,"grammar":g}
                path=out/(lane+"_best.tm")
                builder.tm.save(str(path))
                best["named_table_sha256"]=hashlib.sha256(path.read_bytes()).hexdigest()
                best["constructor_contract_cases"]=constructor_checks(builder,execute_helper)
                minimizers=[seed]
                print(json.dumps({"lane":lane,"new_minimum":cost,"seed":seed}),flush=True)
            elif cost==best["working_states"]:
                minimizers.append(seed)
        results[lane]={"control":control_record,"best":best,"minimizers":minimizers,
                       "distribution":dict(sorted(costs.items())),"macro_word":program,
                       "macro_word_sha256":hashlib.sha256(json.dumps(program,separators=(",",":")).encode()).hexdigest()}
    evidence={"pinned_proveit_head":grammar.PINNED_HEAD,"upstream_commit":rwd.COMMIT,
              "script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "grammar_script_sha256":hashlib.sha256(Path(grammar.__file__).read_bytes()).hexdigest(),
              "codec":{"Truth":0,"Bottom":1,"Imp":"3P","Rel":"3P+4","All":"3P+2"},
              "source_macro_closed_bounds":closed,"seed_range":[0,args.seeds],"exponent":4,
              "results":results,"original_rho6_retained":True,
              "complete_first_order_calculus_proved":False,
              "compiler_simulation_proved":False,"new_ZFC_state_bound_claimed":False}
    (out/"bottom3-results.json").write_text(json.dumps(evidence,indent=2,sort_keys=True)+"\n")
    print(json.dumps({lane:{"control":r["control"]["working_states"],
                           "best":r["best"]} for lane,r in results.items()}),flush=True)


if __name__=="__main__":
    main()
