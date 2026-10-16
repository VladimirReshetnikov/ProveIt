#!/usr/bin/env python3
"""Exact-word grammar experiment for the full-equality EPSC control.

Adapts the user's incoming batch's weighted Re-Pair and finite operation-
bisimulation checker. All changed objects stay in the output directory.
The search changes only bracketing/sharing of a fixed AX word per recipe;
it keeps the complete equality logic, base-four coding, and runtime backend.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib
import importlib.util
import itertools
import json
from pathlib import Path
import sys
from full_equality_epsc import empty_psc, ORDERS
from macro_contract import read_dag, possible_returns, MACROS, NORMAL


def jwrite(path,data):
    path.write_text(json.dumps(data,indent=2,sort_keys=True)+"\n")


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo",type=Path,required=True)
    ap.add_argument("--incoming",type=Path,required=True,
                    help="unpacked zfc_one_schema_research directory")
    ap.add_argument("--scratch",type=Path,required=True)
    ap.add_argument("--seeds",type=int,default=128)
    ap.add_argument("--search",action="store_true",
                    help="repeat the selected 2048-case search; otherwise build the fixed winning recipe")
    args=ap.parse_args()
    repo,out=args.repo.resolve(),args.scratch.resolve()
    if out==repo or repo in out.parents:
        ap.error("output must be outside the input checkout")
    out.mkdir(parents=True,exist_ok=True)
    grammar_helper=args.incoming.resolve()/"machine/rebracket_axioms.py"
    if hashlib.sha256(grammar_helper.read_bytes()).hexdigest() != "bdbf5a84ab1a2914e351e917d7ff3994fec5729bddbe33971678cd51c2839119":
        ap.error("incoming rebracketing helper differs from its pinned bytes")
    spec=importlib.util.spec_from_file_location("incoming_rebracket",grammar_helper)
    g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
    sys.path.insert(0,str(repo/"Computability/BusyBeaver/Research/ZFC"))
    import theory_backend_experiment as t
    from recover_wade_dag import git_bytes
    for name in ("TMBuilder.py","tm.py","tmdb.py","LICENSE.wade"):
        (out/name).write_bytes(git_bytes(None,"ZF/generator/"+name))
    sys.path.insert(0,str(out));backend=importlib.import_module("TMBuilder")
    nodes,names,_=read_dag(repo/"lib/jeff-busy-beaver-zfc254/ZF/m254/coq/prog/Dag254.v")
    effects=possible_returns(nodes)
    if any(effects[q]!={NORMAL} for q in MACROS):
        raise ValueError("nonclosed macro")
    logic,_=t.published_spec();original=logic["ax_rows"]("a","h","b","c","u")
    E=empty_psc(t,True)
    V=t.Imp(t.Rel("a","b"),t.All("c",t.Rel("a","b")))
    Q=t.Imp(t.Eq("a","b"),t.All("c",t.Eq("a","b")))
    best=None;distribution={};cases=0;winning=None
    chosen_orders=ORDERS if args.search else (ORDERS[0],)
    chosen_associations=(0,1) if args.search else (0,)
    chosen_seeds=range(args.seeds) if args.search else (0,)
    for oi,order in enumerate(chosen_orders):
        for association in chosen_associations:
            bundle=t.And(t.And(E,Q),V) if association==0 else t.And(E,t.And(Q,V))
            word=[166,121,180,176]
            for i in order:word+=t.emit(original[i])
            word+=t.emit(bundle)+t.TAIL
            expected=["old_top",original[0]]+[original[i] for i in order]+[bundle]
            if t.symbolic(word)[0]!=expected:
                raise ValueError("source-word formula mismatch")
            for seed in chosen_seeds:
                seq,grammar=g.repair(word,seed,4)
                newnodes,newnames,newroot=g.transform(nodes,names,seq,grammar)
                # Early screen on decision nodes: framework costs at least 62.
                if best is not None and len(newnodes)+62>best:
                    cost="pruned_above_best"
                else:
                    machine=g.compile_dag(backend,newnodes,newnames)
                    working={q for q,_ in machine.states}
                    cost=len(working)
                    if best is None or cost<best:
                        best=cost
                        winning={"logical_indices":order,"association":association,
                                 "seed":seed,"alpha":4,"word":word,"seq":seq,"grammar":grammar,
                                 "nodes":newnodes,"names":newnames,"root":newroot}
                        machine.save(str(out/"best_named.tm"))
                        print(json.dumps({"new_minimum":best,"decision_states":len(newnodes),
                                          "logical_indices":order,"association":association,
                                          "seed":seed}),flush=True)
                distribution[str(cost)]=distribution.get(str(cost),0)+1;cases+=1
    if winning is None:raise ValueError("no search result")
    nn,nam,root=winning["nodes"],winning["names"],winning["root"]
    byname={s:q for q,s in nam.items()}
    boundary={byname[names[q]]:q for q in MACROS if names[q] in byname}
    def expansion(q):
        if q in boundary:return [boundary[q]]
        result=[]
        for edge in nn[q]:
            if not edge.startswith("ENode "):
                raise ValueError("nonsequential AX tree")
            result+=expansion(int(edge.split()[1]))
        return result
    if expansion(root)!=winning["word"]:raise ValueError("AX word changed")
    machine=g.compile_dag(backend,nn,nam);g.reextract(machine,nn,nam)
    # Compare with the exact same source word under a plain right comb.
    naive,naivenames,naiveroot=g.transform(nodes,names,winning["word"],[])
    cert,stats=g.bisimulation(naive,nn)
    jwrite(out/"rm_bisimulation.json",cert)
    jwrite(out/"source_dag.json",{"root":0,"axioms_root":naiveroot,"nodes":naive,"names":naivenames})
    jwrite(out/"candidate_dag.json",{"root":0,"axioms_root":root,"nodes":nn,"names":nam})
    working={q for q,_ in machine.states};framework={q for q in working if q[0].isdigit()}
    missing=[(q,b) for q in working for b in ("0","1") if (q,b) not in machine.states]
    if missing!=[("1.inc","1")]:raise ValueError("unexpected missing transition")
    ordered=[machine.start]+sorted(working-{machine.start});number={q:i for i,q in enumerate(ordered)}
    number["halt"]=len(ordered);total=["#! start 0"]
    for q in ordered:
        for b in ("0","1"):
            a=machine.states.get((q,b))
            w,d,dest=(b,"R",number["halt"]) if a is None else (a.write,a.direction,number[a.nextstate])
            total.append(f"{number[q]} {b} {w} {d} {dest}")
    (out/"best_total.tm").write_text("\n".join(total)+"\n")
    jwrite(out/"state_names.json",{"names":ordered,"halt":len(ordered)})
    results={"status":"uncalibrated complete-equality EPSC compiler experiment",
             "working_states":len(working),"decision_states":len(nn),"framework_states":len(framework),
             "transition_rows":len(machine.states),"totalized_transition_rows":len(total)-1,
             "search_cases":cases,"cost_distribution":distribution,
             "search_requested":args.search,"full_selected_family_seeds_per_recipe":args.seeds,
             "search_screen":"skip candidates with decision count + 62 above current measured best; the 62 floor is used only as a search heuristic, not a minimality claim",
             "winner":{k:v for k,v in winning.items() if k not in ("nodes","names")},
             "word_reexpansion_exact":True,"all_helper_return_effects_normal":True,
             "full_equality_logical_interface_unchanged":True,"base4_unchanged":True,
             "all_emitted_decision_edges_reextracted_exactly":True,
             "rm_bisimulation":stats,
             "rm_certificate_sha256":hashlib.sha256((out/"rm_bisimulation.json").read_bytes()).hexdigest(),
             "named_table_sha256":hashlib.sha256((out/"best_named.tm").read_bytes()).hexdigest(),
             "totalized_table_sha256":hashlib.sha256((out/"best_total.tm").read_bytes()).hexdigest(),
             "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             "incoming_grammar_helper_sha256":hashlib.sha256(grammar_helper.read_bytes()).hexdigest(),
             "no_new_verified_state_bound":True}
    jwrite(out/"results.json",results)
    print(json.dumps({k:v for k,v in results.items() if k!="winner"},indent=2))


if __name__=="__main__":main()
