#!/usr/bin/env python3
"""Measure empty-seeded PSC with the complete original equality calculus.

This keeps all eight original logical schemas, both atomic vacuity schemas,
base-four formula coding, proof enumeration, register layout, and the pinned
Wade backend. Only the theory emission, formula/row order and exact sequence
sharing change. No new consistency-machine certification is asserted.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib
import itertools
import json
from pathlib import Path
import sys

ORDERS = (
    (1,2,3,4,5,6,7,8),
    (8,7,6,5,4,3,2,1),
    (1,7,5,3,2,4,6,8),
    (1,3,5,7,2,4,6,8),
    (2,4,6,8,1,7,5,3),
    (1,2,7,8,5,6,3,4),
    (1,8,7,6,5,4,3,2),
    (7,5,3,1,8,6,4,2),
)


def empty_psc(t, support_first):
    I,A,E,N,O,R = t.Imp,t.All,t.Ex,t.And,t.Or,t.Rel
    c = "c"
    bound = A(0,E(c,A(1,I(c,A(0,I(R(0,1),R(0,c)))))))
    empty = A(c,t.Not(R(c,0)))
    closure = A(0,I(O(empty,R(0,c)),A(1,I(c,R(1,c)))))
    support = A(1,I(R(1,c),E(0,c)))
    return I(bound,E(c,N(support,closure) if support_first else N(closure,support)))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", type=Path, required=True)
    ap.add_argument("--scratch", type=Path, required=True)
    args = ap.parse_args()
    repo, out = args.repo.resolve(), args.scratch.resolve()
    if out == repo or repo in out.parents:
        ap.error("scratch must be outside the input checkout")
    out.mkdir(parents=True,exist_ok=True)
    sys.path.insert(0,str(repo/"Computability/BusyBeaver/Research/ZFC"))
    import theory_backend_experiment as t
    from recover_wade_dag import builder_from_dag, git_bytes, parse_dag
    for name in ("TMBuilder.py","tm.py","tmdb.py","LICENSE.wade"):
        (out/name).write_bytes(git_bytes(None,"ZF/generator/"+name))
    sys.path.insert(0,str(out))
    backend = importlib.import_module("TMBuilder")
    nodes,names = parse_dag(git_bytes(None,"ZF/m254/coq/prog/Dag254.v").decode())
    spec,_ = t.published_spec()
    original = spec["ax_rows"]("a","h","b","c","u")
    V = t.Imp(t.Rel("a","b"),t.All("c",t.Rel("a","b")))
    Q = t.Imp(t.Eq("a","b"),t.All("c",t.Eq("a","b")))
    results = []
    best = None
    for order, components, grouping, support_first in itertools.product(
            ORDERS,itertools.permutations("EVQ"),(0,1),(False,True)):
        E = empty_psc(t,support_first)
        x,y,z = [{"E":E,"V":V,"Q":Q}[key] for key in components]
        bundle = t.And(t.And(x,y),z) if grouping == 0 else t.And(x,t.And(y,z))
        word = [166,121,180,176]
        for i in order:
            word += t.emit(original[i])
        word += t.emit(bundle)+t.TAIL
        symbolic,_ = t.symbolic(word)
        if symbolic != ["old_top",original[0]]+[original[i] for i in order]+[bundle]:
            raise ValueError("independent symbolic stack mismatch")
        builder = builder_from_dag(backend,nodes,names)
        builder.sequence_lookup = {s.seq:i for i,s in enumerate(builder.sequences)}
        name = "full_eq_epsc_"+"".join(map(str,order))+"_"+"".join(components)+"_"+str(grouping)+str(int(support_first))
        t.lower_program(builder,nodes,word,name,shared=True,base3=False)
        builder.generate();builder.tm.gc()
        states = {q for q,_ in builder.tm.states}
        path = out/(name+".tm")
        builder.tm.save(str(path))
        row = {"name":name,"working_states":len(states),
               "framework_states":sum(q[0].isdigit() for q in states),
               "decision_states":sum(not q[0].isdigit() for q in states),
               "explicit_transition_rows":len(builder.tm.states),
               "AX_macro_count":len(word),"EPSC_macro_count":len(t.emit(E)),
               "equality_constructor_retained":any(q.startswith("weq(") for q in states),
               "logical_indices":order,"logical_rho_order":[9-i for i in order],
               "bundle_components":components,"right_associated":bool(grouping),
               "support_first":support_first,
               "table_sha256":hashlib.sha256(path.read_bytes()).hexdigest()}
        results.append(row)
        if best is None or row["working_states"] < best:
            best = row["working_states"]
    distribution = {}
    for row in results:
        distribution[row["working_states"]] = distribution.get(row["working_states"],0)+1
    evidence = {"status":"uncalibrated full-equality PSC compiler control",
                "base_four_unchanged":True,"dual_rho6_used":False,
                "original_all_eight_logical_schemas":True,
                "both_atomic_vacuities":True,"local_lowcode_gate":False,
                "original_c_ne_a_b_gate_tail_preserved":True,
                "finite_selected_search_cases":len(results),"minimum_working_states":best,
                "state_distribution":distribution,
                "minimizers":[row for row in results if row["working_states"] == best],
                "all_results":results,
                "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                "scope":"A measured full-equality comparison program. This keeps the original logical interface but still needs a theory-emission/completeness and compiler/initializer proof for the new literal table."}
    (out/"results.json").write_text(json.dumps(evidence,indent=2,sort_keys=True)+"\n")
    print(json.dumps({k:v for k,v in evidence.items() if k!="all_results"},indent=2))


if __name__ == "__main__":
    main()
