"""Price all eight original logical rows with Eq replaced by two-sided twins.

The local quantified label for Delta(i,j) is the computed numeral
k=3*P(i,j)+1, obtained by the existing Rel constructor. Thus k>i,j and no new
register operation or freshness gate is needed. This is a compiler control,
not a theorem that the resulting enumerator proves full first-order logic.
"""
from pathlib import Path
import hashlib
import importlib
import json
import sys

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/"repo/Computability/BusyBeaver/Research/ZFC"))
sys.path.insert(0,str(ROOT/"repo/lib/jeff-busy-beaver-zfc254/ZF/generator"))
import theory_backend_experiment as t
from recover_wade_dag import builder_from_dag,git_bytes,parse_dag


def delta(i,j):
    # This Rel AST computes a natural label, not an atom inside the binder.
    k=t.Rel(i,j)
    incoming=t.All(k,t.Iff(t.Rel(k,i),t.Rel(k,j)))
    outgoing=t.All(k,t.Iff(t.Rel(i,k),t.Rel(j,k)))
    return t.And(incoming,outgoing)


def translate(f):
    if not isinstance(f,tuple):
        return f
    kind,a,b=f
    if kind=="eq":
        return delta(a,b)
    if kind=="all":
        return t.All(a,translate(b))
    if kind=="rel":
        return f
    assert kind=="imp"
    return t.Imp(translate(a),translate(b))


def main():
    backend=importlib.import_module("TMBuilder")
    nodes,names=parse_dag(git_bytes(None,"ZF/m254/coq/prog/Dag254.v").decode())
    spec,digest=t.published_spec()
    rows=[translate(x) for x in spec["ax_rows"]("a","h","b","c","u")]
    bundle=translate(spec["bundle"]("a","b","c"))
    program=[166,121,180,176]
    for row in rows[1:]:
        program+=t.emit(row)
    program+=t.emit(bundle)+t.TAIL
    assert 182 not in program
    actual,_=t.symbolic(program)
    assert actual==["old_top"]+rows+[bundle]
    builder=builder_from_dag(backend,nodes,names)
    builder.sequence_lookup={s.seq:i for i,s in enumerate(builder.sequences)}
    t.lower_program(builder,nodes,program,"twosided_Delta_control",shared=True,base3=True)
    builder.generate()
    builder.tm.gc()
    states={q for q,_ in builder.tm.states}
    table=ROOT/"twosided-Delta-control.named.tm"
    builder.tm.save(str(table))
    pair=lambda a,b:(a+b)*(a+b+1)//2+b
    freshness_cases=0
    for i in range(128):
        for j in range(128):
            k=3*pair(i,j)+1
            assert k>i and k>j
            freshness_cases+=1
    result={"pinned_ProveIt_commit":"17d0f2eaa650901cda59764dfcc4661c199e49c8",
        "comparison":"GEN plus all8 original logical rows; Eq translated to two-sided Delta",
        "formula_coding":"base3",
        "fresh_binder":"k=3*P(i,j)+1; computed by existing Rel constructor",
        "theory_bundle":"original C/G/member-vacuity/translated-equality-vacuity",
        "original_logical_order_retained":True,
        "common_subsequence_extraction":True,
        "new_register_operations":0,
        "working_states":len(states),
        "framework_states":sum(q[0].isdigit() for q in states),
        "decision_states":sum(not q[0].isdigit() for q in states),
        "explicit_transition_rows":len(builder.tm.states),
        "expanded_macro_count":len(program),
        "equality_constructor_reachable":any(q.startswith("weq(") for q in states),
        "symbolic_macro_roundtrip_exact":True,
        "finite_binder_freshness_cases":freshness_cases,
        "source_spec_sha256":digest,
        "script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "table_sha256":hashlib.sha256(table.read_bytes()).hexdigest(),
        "full_enumerator_or_compiler_calibration_claimed":False,
        "minimum_in_a_larger_family_claimed":False}
    (ROOT/"twosided-Delta-control-results.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))


if __name__=="__main__":
    main()
