#!/usr/bin/env python3
"""Reproduce all initializer and exact-quotient compiler controls offline.

Usage: python -B reproduce.py
Optional --repo and --upstream select full checkouts instead of bundled sources.
The checkout and upstream source are read only. Outputs go under --output.
Only Python's standard library and the identified source modules are needed.
"""
from __future__ import annotations
import argparse, hashlib, json, sys
from pathlib import Path

from contiguous_initializer import choose_parameters, make_initializer, check_literal_boot
from exact_quotient import minimize, verify_certificate, encode, parse


def digest(data): return hashlib.sha256(data).hexdigest()


def construct(m, base, initial, shared):
    minimum = base.evidence["requested_minimum_gap"]
    n,stride = choose_parameters(minimum, shared_cleanup=shared)
    init,contract = make_initializer(initial,n,stride,"d:0",shared_cleanup=shared)
    inverse = {q:name for name,q in base.labels.items()}
    runtime = {(inverse[q],b):(w,d,inverse[t])
               for (q,b),(w,d,t) in base.table.items() if not inverse[q].startswith("i:")}
    if shared:
        # These rows, followed by the unchanged dispatcher, implement cleanup.
        assert runtime["e:14",0] == (0,"L","e:20")
        assert runtime["e:20",1] == (0,"L","e:2")
        assert runtime["e:2",0] == (0,"L","e:2")
        assert runtime["e:2",1] == (1,"L","e:4")
        chain = [4,6,9,13,19,29,41,58,74]
        for j,q in enumerate(chain):
            assert runtime[f"e:{q}",0] == (
                (0,"L",f"e:{chain[j+1]}") if j+1<len(chain) else (0,"L","e:84"))
        assert runtime["e:84",0] == (0,"R","e:84")
        assert runtime["e:84",1] == (1,"R","d:0")
        # The shared exit assumes the nine-state dispatcher, as in these inputs.
        assert base.evidence["dispatcher_threshold"] == 9
    labeled = runtime | init
    order = ["i:0"] + sorted({q for q,b in labeled}-{"i:0"})
    labels = {q:j for j,q in enumerate(order)}
    labels["halt"] = len(order)
    table = {(labels[q],b):(w,d,labels[t]) for (q,b),(w,d,t) in labeled.items()}
    machine = m.MiraMachine(table,labels,base.sites,{},contract["gap"],tuple(initial))
    contract["minimum_required_gap"] = minimum
    assert contract["gap"] >= minimum
    return machine,contract


def load_json_dag(path):
    obj = json.loads(path.read_text())
    old_root = obj["root"]
    remap = {old_root:0} | {q:j+1 for j,q in enumerate(sorted(int(k) for k in obj["nodes"] if int(k)!=old_root))}
    def edge(value):
        if isinstance(value,str):
            if value.startswith("ENode "): return f"ENode {remap[int(value.split()[1])]}"
            return value
        kind = {"N":"ENode","I":"EInc","D":"EDecnz","B":"EBreak","C":"EContinue","H":"EHalt"}[value[0]]
        return kind if kind=="EHalt" else f"{kind} {remap[value[1]] if kind=='ENode' else value[1]}"
    nodes = {remap[int(q)]:tuple(edge(e) for e in row) for q,row in obj["nodes"].items()}
    names = {q:f"source_node_{q}" for q in nodes}
    return nodes,names


def main():
    if not __debug__: raise RuntimeError("Run with assertions enabled")
    parser = argparse.ArgumentParser(description=__doc__)
    here = Path(__file__).resolve().parent
    parser.add_argument("--repo",type=Path,default=here/"vendor/proveit")
    parser.add_argument("--upstream",type=Path,default=here/"vendor/upstream")
    parser.add_argument("--output",type=Path,default=Path(__file__).resolve().parent/"results")
    args = parser.parse_args()
    repo,upstream,out = args.repo.resolve(),args.upstream.resolve(),args.output.resolve()
    if out == repo or repo in out.parents or out == upstream or upstream in out.parents:
        raise ValueError("output must be outside both source checkouts")
    out.mkdir(parents=True,exist_ok=True)
    sys.dont_write_bytecode = True
    source = repo/"Computability/BusyBeaver/Research/ZFC"
    sys.path.insert(0,str(source))
    import recover_wade_dag as r
    r.SNAPSHOT = upstream
    import mira_backend as m
    import compact_initializer as previous
    raw_dag = r.git_bytes(None,"ZF/m254/coq/prog/Dag254.v")
    original = r.parse_dag(raw_dag.decode())
    host = repo/"SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data"
    paths = {
        "original219": upstream/"ZF/m254/coq/prog/Dag254.v",
        "rebracket206": host/"19-subst-engineering-artifacts-full_logic_best.dag.json",
        "decoder202": host/"20-complete-vendor-decoder255-data-candidate202.json",
    }
    dags = {"original219":original,
            **{label:load_json_dag(path) for label,path in paths.items() if label!="original219"}}
    records=[]
    for label,(nodes,names) in dags.items():
        for seed in (0,2):
            initial = [seed]+[0]*8
            base = m.compile_dag(nodes,names,initial_registers=initial,initializer="compact")
            old_contract = dict(base.evidence["compact_initializer_contract"])
            old_contract["absolute_exit_head"] = -(18+sum(initial)+base.gap)
            old_contract["minimum_required_gap"] = base.evidence["requested_minimum_gap"]
            variants = [("previous",base,old_contract)]
            variants += [("contiguous_shared" if shared else "contiguous",*construct(m,base,initial,shared))
                         for shared in (False,True)]
            for variant,machine,contract in variants:
                name = f"{label}_np{seed}_{variant}"
                raw = encode(machine.table)
                (out/(name+".tm")).write_bytes(raw)
                boot = check_literal_boot(machine.table,0,machine.root,contract)
                quotient,cert = minimize(machine.table)
                qbytes = encode(quotient)
                (out/(name+"_quotient.tm")).write_bytes(qbytes)
                (out/(name+"_quotient.json")).write_text(json.dumps(cert,indent=2)+"\n")
                # Independent reparse, then the complete rowwise homomorphism check.
                verify_certificate(parse(raw),parse(qbytes),cert)
                qlabels = {name:cert["state_map"][q] for name,q in machine.labels.items()}
                qmachine = m.MiraMachine(quotient,qlabels,machine.sites,{},machine.gap,tuple(initial))
                qboot = check_literal_boot(quotient,0,qmachine.root,contract)
                assert boot["head"]==qboot["head"] and boot["one_positions"]==qboot["one_positions"]
                # All changed initializer variants have the exact same runtime.
                # One symbolic check per DAG/seed/initializer gap checks the whole
                # compiled quotient at every site, with opaque arbitrary registers.
                sites = qmachine.check_sites()
                inverse = {q:name for name,q in machine.labels.items()}
                record = dict(name=name,dag=label,seed=seed,input_dag_nodes=len(nodes),
                              raw_states=len(machine.table)//2,quotient_states=len(quotient)//2,
                              source_sha256=digest(raw),quotient_sha256=digest(qbytes),
                              contract=contract,boot=boot,quotient_boot=qboot,
                              quotient_classes=[[inverse[q] for q in group] for group in cert["nontrivial_classes"]],
                              symbolic_runtime_checks=sites,exact_quotient_certificate_passed=True,
                              original_compiler_evidence=base.evidence)
                records.append(record)
                print(name,record["raw_states"],"->",record["quotient_states"],
                      "gap",contract["gap"],"steps",contract["blank_steps"],flush=True)
    # Systematic boundary checks exercise the general formula, not just the large controls.
    boundary = shared_boundary = 0
    inverse = {q:name for name,q in base.labels.items()}
    runtime = {(inverse[q],b):(w,d,inverse[t])
               for (q,b),(w,d,t) in base.table.items() if not inverse[q].startswith("i:")}
    for n in range(1,13):
        for stride in range(1,13):
            for initial in ([0]*9,[2]+[0]*8,list(range(9))):
                table,contract = make_initializer(initial,n,stride)
                check_literal_boot(table,"i:0","return",contract)
                boundary += 1
                table,contract = make_initializer(initial,n,stride,"d:0",shared_cleanup=True)
                check_literal_boot(runtime|table,"i:0","d:0",contract)
                shared_boundary += 1
    baseline_controls = []
    for label,path in (
        ("published254",upstream/"ZF/m254/machine/zfc_254.tm"),
        ("published253",host/"04-machine-machines-zfc_253.tm")):
        data = path.read_bytes()
        table = parse(data)
        quotient,cert = minimize(table)
        assert len(table) == len(quotient)
        assert cert["nontrivial_classes"] == []
        raw,qraw = encode(table),encode(quotient)
        (out/(label+".tm")).write_bytes(raw)
        (out/(label+"_quotient.tm")).write_bytes(qraw)
        (out/(label+"_quotient.json")).write_text(json.dumps(cert,indent=2)+"\n")
        baseline_controls.append(dict(name=label,source_sha256=digest(data),
                                      normalized_sha256=digest(raw),
                                      states=len(table)//2,quotient_states=len(quotient)//2,
                                      nontrivial_classes=[],strict_stepwise_quotient_found=False))
    evidence = dict(status="passed",scope="compiler controls; no new ZFC machine bound",
                    upstream_commit=r.COMMIT,
                    inputs={str(path.relative_to(repo) if repo in path.parents else path.relative_to(upstream)):digest(path.read_bytes())
                            for path in paths.values()},
                    compiler_sources={f:digest((source/f).read_bytes())
                                      for f in ("mira_backend.py","compact_initializer.py","recover_wade_dag.py")},
                    local_sources={f:digest((Path(__file__).resolve().parent/f).read_bytes())
                                   for f in ("reproduce.py","contiguous_initializer.py","exact_quotient.py")},
                    standalone_formula_boundary_checks=boundary,
                    shared_formula_boundary_checks=shared_boundary,records=records,
                    baseline_quotient_controls=baseline_controls,
                    new_consistency_calibration_proved=False,new_arbitrary_register_box_proof=False,
                    initializer_invariant_ordinary_mathematical_proof=True,
                    exact_quotient_preserves_every_input_by_transition_homomorphism=True)
    (out/"evidence.json").write_text(json.dumps(evidence,indent=2,sort_keys=True)+"\n")


if __name__ == "__main__": main()
