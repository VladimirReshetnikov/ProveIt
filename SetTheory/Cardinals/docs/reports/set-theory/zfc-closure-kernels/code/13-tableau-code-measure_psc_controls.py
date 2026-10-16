#!/usr/bin/env python3
"""Measure PSC compilers retaining the complete original logical subsystem.

Requires a ProveIt checkout/snapshot with the public pinned vendor files.
Every emitted machine is an uncalibrated compiler control, not a new bound.
The original generator and vendor snapshot are read only.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib
import json
from pathlib import Path
import sys


PROVEIT_COMMIT = "17d0f2eaa650901cda59764dfcc4661c199e49c8"
GENERATOR_HASHES = {
    "theory_backend_experiment.py": "37043e71a02fba57337040100d79e8f92cba5e2ac5efead816b1522b8663a2e1",
    "recover_wade_dag.py": "caa4996be46f9201991dba07f81d4673f14e874ac682226c29fce9e0cea851f1",
    "pairing_backend_experiment.py": "18f6cf1a50514581834daecd542d9855d07d6c522d4d70f906241de035423572",
}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    repo, out = args.repo.resolve(), args.output.resolve()
    if out == repo or repo in out.parents:
        ap.error("output must be outside the source repository")
    out.mkdir(parents=True, exist_ok=True)
    zfc = repo / "Computability/BusyBeaver/Research/ZFC"
    for filename, expected in GENERATOR_HASHES.items():
        if hashlib.sha256((zfc / filename).read_bytes()).hexdigest() != expected:
            raise ValueError(f"ProveIt generator differs from pinned commit: {filename}")
    sys.path.insert(0, str(zfc))
    import theory_backend_experiment as exp
    import recover_wade_dag as recovery
    for name in ("TMBuilder.py", "tm.py", "tmdb.py", "LICENSE.wade"):
        (out / name).write_bytes(recovery.git_bytes(None, "ZF/generator/" + name))
    nodes, names = recovery.parse_dag(
        recovery.git_bytes(None, "ZF/m254/coq/prog/Dag254.v").decode())
    sys.path.insert(0, str(out))
    backend = importlib.import_module("TMBuilder")
    _, logical, old_contract = exp.old_contract(nodes)
    original, vacuity = exp.theory_rows()
    I, R, A, E, W, O = exp.Imp, exp.Rel, exp.All, exp.Eq, exp.Ex, exp.Or
    c = "c"
    sb = A(0, W(c, A(1, I(c, A(0, I(R(0, 1), R(0, c)))))))
    supported = A(1, I(R(1, c), W(0, c)))

    def psc(seed):
        closed = A(0, I(O(seed, R(0, c)), A(1, I(c, R(1, c)))))
        return I(sb, A(1, W(c, exp.And(closed, supported))))

    point = psc(E(0, 1))
    subset = psc(A(c, I(R(c, 0), R(c, 1))))
    results = []
    for label, theory, gated in (("extensional_point_PSC", original, True),
                                 ("raw_point_PSC", point, True),
                                 ("raw_subset_PSC", subset, True),
                                 ("raw_point_PSC_ungated", point, False),
                                 ("raw_subset_PSC_ungated", subset, False)):
        for sharing in (False, True):
            builder = recovery.builder_from_dag(backend, nodes, names)
            builder.sequence_lookup = {s.seq: i for i, s in enumerate(builder.sequences)}
            regs = [builder.reg(n) for n in recovery.REGISTERS]
            clear_top = builder.while_decnz(regs[1], ())
            local_gate = [192, builder.while_decnz(regs[7], regs[3].inc),
                          builder.if_not_decnz(regs[6], clear_top),
                          builder.if_not_decnz(regs[6], clear_top),
                          builder.while_decnz(regs[6], ())]
            program = logical + exp.emit(theory) + (local_gate if gated else []) + exp.emit(vacuity) + exp.TAIL
            mode = label + ("_shared" if sharing else "_plain")
            exp.lower_program(builder, nodes, program, mode, shared=sharing, base3=False)
            builder.generate()
            builder.tm.gc()
            filename = out / (mode + ".tm")
            builder.tm.save(str(filename))
            states = {q for q, _ in builder.tm.states}
            results.append({
                "variant": mode,
                "formula_constructor_macros_in_theory": len(exp.emit(theory)),
                "local_c_ge_2_theory_gate": gated,
                "working_states": len(states),
                "decision_states": sum(not q[0].isdigit() for q in states),
                "framework_states": sum(q[0].isdigit() for q in states),
                "transition_rows": len(builder.tm.states),
                "missing_rows": [(q, b) for q in sorted(states) for b in ("0", "1")
                                 if (q, b) not in builder.tm.states],
                "table_sha256": hashlib.sha256(filename.read_bytes()).hexdigest(),
            })
    result = {
        "status": "measured, uncalibrated compiler controls",
        "proveit_commit": PROVEIT_COMMIT,
        "proveit_generator_sha256": GENERATOR_HASHES,
        "upstream_commit": recovery.COMMIT,
        "logical_kernel": "All eight original logical schemas, old rho6, GEN, MP, original equality coding; no equality-rule deletion",
        "coding": "Original base4 formula coding and Cantor proof/stack coding",
        "gates": "Separate original membership/equality vacuity; c>=2 only on PSC theory row for gated variants; original c!=a,b gates retained on vacuity in every variant",
        "subset_seed_ast": subset,
        "original_AX_recovery": old_contract,
        "variants": results,
        "scope": "Measured emitted tables only. No simulation, dynamic-binder schema coverage, or whole-machine consistency bridge is proved by this script.",
    }
    (out / "measurements.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k not in ("subset_seed_ast", "original_AX_recovery")}, indent=2))


if __name__ == "__main__":
    main()
