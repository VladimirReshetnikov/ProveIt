"""Regenerate the fixed 250-state conjunction-commutation candidate.

Requires the pinned sources fetched by reproduce.py. It makes the three
specified conjunction changes, preserves all registers/gates and emits the
same named table as the exhaustive search, then normalizes and hash-checks it.
No calibrated Con(ZFC) machine claim is made.
"""
from __future__ import annotations
import hashlib
import importlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/"repo/Computability/BusyBeaver/Research/ZFC"))
sys.path.insert(0,str(ROOT/"repo/lib/jeff-busy-beaver-zfc254/ZF/generator"))
import theory_backend_experiment as t
from recover_wade_dag import builder_from_dag, git_bytes, parse_dag
from audit_raw_candidate import normalize_named
from search_conjunctions import variants

NAMED_HASH = "799ec421e41533229cb24aa172f61fc637d3435466d8d0f2eff0fcadf2cdcfc6"
TOTAL_HASH = "d7af3920268db1c95bf71dc06b77e53c8266086a13043b2fc91f9319c520aff1"


def main():
    for name in ("TMBuilder.py","tm.py","tmdb.py","LICENSE.wade"):
        git_bytes(None,"ZF/generator/"+name)
    backend=importlib.import_module("TMBuilder")
    nodes,names=parse_dag(git_bytes(None,"ZF/m254/coq/prog/Dag254.v").decode())
    spec,digest=t.published_spec()
    C=variants(spec["bundle_C"]("a","b","c"))[2][0]
    G=variants(spec["bundle_G"]("a","b","c"))[1][0]
    V=t.Imp(t.Rel("a","b"),t.All("c",t.Rel("a","b")))
    logical=spec["ax_rows"]("a","h","b","c","u")
    logical[3]=t.Imp("b",t.All("a",t.Ex("a","b")))
    order=(1,7,5,3)
    bundle=t.And(t.And(V,C),G)
    program=[166,121,180,176]
    for index in order:
        program+=t.emit(logical[index])
    program+=t.emit(bundle)+t.TAIL
    actual,_=t.symbolic(program)
    assert actual == ["old_top"]+[logical[i] for i in (0,*order)]+[bundle]
    builder=builder_from_dag(backend,nodes,names)
    builder.sequence_lookup={s.seq:i for i,s in enumerate(builder.sequences)}
    t.lower_program(builder,nodes,program,"and_commute_search",shared=True,base3=True)
    builder.generate()
    builder.tm.gc()
    states={q for q,_ in builder.tm.states}
    assert len(states)==250 and len(builder.tm.states)==499
    named=ROOT/"conjunction-candidate-250.named.tm"
    builder.tm.save(str(named))
    assert hashlib.sha256(named.read_bytes()).hexdigest()==NAMED_HASH
    total,mapping,evidence=normalize_named(named.read_bytes())
    assert hashlib.sha256(total).hexdigest()==TOTAL_HASH
    (ROOT/"conjunction-candidate-250.tm").write_bytes(total)
    result={"working_states":250,"transition_rows":500,
        "named_sha256":NAMED_HASH,"normalized_sha256":TOTAL_HASH,
        "decision_states":sum(not q[0].isdigit() for q in states),
        "framework_states":sum(q[0].isdigit() for q in states),
        "relative_falsity_commutations_only":True,
        "symbolic_roundtrip_exact":True,
        "calibrated_ConZFC_machine_claimed":False,
        "normalization":evidence}
    (ROOT/"candidate250-generation.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))


if __name__=="__main__":
    main()
