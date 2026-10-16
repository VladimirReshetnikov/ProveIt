"""Measure old-rho6/base3 and explicit-explosion repairs without changing252.

Offline source pins and exact-macro sharing come from the existing experiment.
All backend execution and generated partial named tables stay in external
scratch. This script supplies compiler measurements, not a calculus proof.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import importlib
import itertools
import json
from pathlib import Path
import sys

from recover_wade_dag import ROOT, COMMIT, builder_from_dag, git_bytes, parse_dag
from theory_backend_experiment import (All, Ex, Imp, Rel, And, TAIL, emit,
                                       lower_program, published_spec)

LANES = ("old-base3", "old-base3-swapped", "dual-efq-b", "dual-efq-a", "dual-efq-c")


def search(backend, nodes, names, scratch, lane):
    spec, _ = published_spec()
    rows = spec["ax_rows"]("a", "h", "b", "c", "u")
    efq = lane.startswith("dual-efq-")
    selected = (1, 3, 5, 7)
    if efq:
        rows[3] = Imp("b", All("a", Ex("a", "b")))
        rows.append(Imp(1, lane[-1]))
        selected += (9,)
    components = {"C": spec["bundle_C"]("a", "b", "c"),
                  "G": spec["bundle_G"]("a", "b", "c"),
                  "V": Imp(Rel("a", "b"), All("c", Rel("a", "b")))}
    costs, best, minimizers, best_sha = Counter(), None, [], None
    output = scratch / f"{lane}-best.tm"
    for order in itertools.permutations(selected):
        for arrangement in itertools.permutations(("C", "G", "V")):
            for right_associated in (False, True):
                x, y, z = [components[k] for k in arrangement]
                bundle = And(x, And(y, z)) if right_associated else And(And(x, y), z)
                program = [166, 121, 180, 176]
                program += [m for i in order for m in emit(rows[i])]
                program += emit(bundle) + TAIL
                builder = builder_from_dag(backend, nodes, names)
                builder.sequence_lookup = {s.seq: i for i, s in enumerate(builder.sequences)}
                lower_program(builder, nodes, program, "repair_" + lane,
                              shared=True, base3=True)
                if lane == "old-base3-swapped":
                    # Retag AFTER sharing: Imp0, Rel2, All1. Constructor roots
                    #180/181 keep their underlying add2/add1 behavior; references
                    #to them exchange. This includes the designated F2 cost.
                    for i, sequence in enumerate(builder.sequences):
                        if i not in (180, 181, 182):
                            sequence.seq = tuple(
                                {180: 181, 181: 180}.get(v, v) if isinstance(v, int) else v
                                for v in sequence.seq)
                    builder.sequences[177].seq = (171, 159)
                    reg = builder.reg("scratch1")
                    target = builder.add_sequence([reg.inc, reg.inc])
                    builder.sequences[152].seq = (target, builder.sequences[152].seq[1])
                    builder.reduce_to_cons()
                    builder.name_sequences()
                builder.generate()
                builder.tm.gc()
                state_count = len({q for q, _ in builder.tm.states})
                costs[state_count] += 1
                descriptor = {"rows_after_GEN": ["EFQ" if i == 9 else f"rho{9-i}"
                                                 for i in order],
                              "bundle_order": arrangement,
                              "bundle_right_associated": right_associated}
                if best is None or state_count < best:
                    best, minimizers = state_count, [descriptor]
                    builder.tm.save(str(output))
                    best_sha = hashlib.sha256(output.read_bytes()).hexdigest()
                elif state_count == best:
                    minimizers.append(descriptor)
    return {"lane": lane, "variants": sum(costs.values()), "minimum_working_states": best,
            "cost_distribution": dict(sorted(costs.items())), "minimizers": minimizers,
            "first_minimum_named_table_sha256": best_sha,
            "source_missing_row": "1.inc/read1 (not totalized here)",
            "calculus_or_compiler_correctness_proved": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scratch", type=Path, required=True)
    parser.add_argument("--lanes", nargs="+", choices=LANES, default=["old-base3"])
    parser.add_argument("--output-evidence", type=Path)
    args = parser.parse_args()
    scratch = args.scratch.resolve()
    if scratch == Path("/") or scratch == ROOT or ROOT in scratch.parents:
        parser.error("scratch must be outside the repository and not filesystem root")
    scratch.mkdir(parents=True, exist_ok=True)
    for name in ("TMBuilder.py", "tm.py", "tmdb.py", "LICENSE.wade"):
        (scratch / name).write_bytes(git_bytes(None, "ZF/generator/" + name))
    nodes, names = parse_dag(git_bytes(None, "ZF/m254/coq/prog/Dag254.v").decode())
    sys.path.insert(0, str(scratch))
    backend = importlib.import_module("TMBuilder")
    results = []
    for lane in args.lanes:
        result = search(backend, nodes, names, scratch, lane)
        results.append(result)
        print(json.dumps({"lane": lane, "variants": result["variants"],
                          "minimum_working_states": result["minimum_working_states"]}), flush=True)
    evidence = {"upstream_commit": COMMIT,
                "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                "base_experiment_sha256": hashlib.sha256(
                    Path(__file__).with_name("theory_backend_experiment.py").read_bytes()).hexdigest(),
                "results": results, "new_ZFC_machine_or_state_bound_claimed": False}
    if args.output_evidence:
        args.output_evidence.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
