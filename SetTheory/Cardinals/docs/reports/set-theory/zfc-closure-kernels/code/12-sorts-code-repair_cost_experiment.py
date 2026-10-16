#!/usr/bin/env python3
"""Measure two diagnostic additions to the uncalibrated raw CODE kernel.

This imports the pinned ProveIt reconstruction and public Wade compiler.
Neither control has a completeness theorem. Counts are compiler costs, not
ZFC consistency-machine bounds. The existing raw 252 baseline is reproduced
before 288 control compilations: 120 bundle layouts per control, then 24
logical-row orders for the first best bundle of each control.
"""
from __future__ import annotations

if not __debug__:
    raise SystemExit("Compiler regressions require enabled assertions; do not use python -O or -OO.")

import argparse
from collections import Counter
import hashlib
import importlib
import itertools
import json
from pathlib import Path
import sys
import time


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def trees(leaves):
    if len(leaves) == 1:
        yield leaves[0]
        return
    for cut in range(1, len(leaves)):
        for left in trees(leaves[:cut]):
            for right in trees(leaves[cut:]):
                yield (left, right)


def formula_of_tree(tree, factors, api):
    if isinstance(tree, str):
        return factors[tree]
    return api.And(formula_of_tree(tree[0], factors, api),
                   formula_of_tree(tree[1], factors, api))


def pretty_tree(tree):
    if isinstance(tree, str):
        return tree
    return f"({pretty_tree(tree[0])} AND {pretty_tree(tree[1])})"


def make_program(api, control, order, tree):
    spec, _ = api.published_spec()
    rows = spec["ax_rows"]("a", "h", "b", "c", "u")
    rows[3] = api.Imp("b", api.All("a", api.Ex("a", "b")))
    U = api.Imp(api.All("c", api.Rel("c", "a")), api.Rel("b", "a"))
    D = api.All("c", api.Iff(api.Rel("c", "a"), api.Rel("c", "b")))
    P = api.Imp(D, api.Imp(api.Rel("a", "c"), api.Rel("b", "c")))
    factors = {"C": spec["bundle_C"]("a", "b", "c"),
               "G": spec["bundle_G"]("a", "b", "c"),
               "V": api.Imp(api.Rel("a", "b"),
                            api.All("c", api.Rel("a", "b"))),
               "U": U, "P": P}
    bundle = formula_of_tree(tree, factors, api)
    program = [166, 121, 180, 176]
    for row in order:
        program += api.emit(rows[row])
    program += api.emit(bundle) + api.TAIL
    actual, _ = api.symbolic(program)
    expected = ["old_top", rows[0]] + [rows[i] for i in order] + [bundle]
    if actual != expected:
        raise ValueError("AX symbolic stack reconstruction failed")
    if 182 in program:
        raise ValueError("An equality constructor was unexpectedly inserted")
    return program, factors[control]


def compile_program(api, backend, nodes, names, program, mode):
    builder = api.builder_from_dag(backend, nodes, names)
    builder.sequence_lookup = {s.seq: i for i, s in enumerate(builder.sequences)}
    api.lower_program(builder, nodes, program, mode, shared=True, base3=True)
    builder.generate()
    builder.tm.gc()
    states = {q for q, _ in builder.tm.states}
    result = {
        "working_states": len(states),
        "decision_states": sum(not q[0].isdigit() for q in states),
        "framework_states": sum(q[0].isdigit() for q in states),
        "explicit_transition_rows": len(builder.tm.states),
        "missing_transition_rows": [[q, b] for q in sorted(states)
                                    for b in ("0", "1") if (q, b) not in builder.tm.states],
        "terminal_targets": sorted({e.nextstate for e in builder.tm.states.values()} - states),
        "equality_helper_reachable": any(q.startswith("weq(") for q in states),
        "expanded_AX_macro_count": len(program),
    }
    return builder, result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    here = Path(__file__).resolve().parent
    parser.add_argument("--repo", type=Path, default=here.parent / "repo")
    parser.add_argument("--backend", type=Path, default=Path("/tmp/zfc-current-backend"))
    parser.add_argument("--output-dir", type=Path, default=here / "repair-costs")
    parser.add_argument("--results", type=Path, default=here / "repair_cost_results.json")
    args = parser.parse_args()
    source = args.repo.resolve() / "Computability/BusyBeaver/Research/ZFC"
    sys.path.insert(0, str(source))
    api = importlib.import_module("theory_backend_experiment")
    args.backend.mkdir(parents=True, exist_ok=True)
    for name in ("TMBuilder.py", "tm.py", "tmdb.py", "LICENSE.wade"):
        wanted = api.git_bytes(None, "ZF/generator/" + name)
        if not (args.backend / name).exists():
            (args.backend / name).write_bytes(wanted)
        if (args.backend / name).read_bytes() != wanted:
            raise ValueError(f"Backend file differs from pinned snapshot: {name}")
    sys.path.insert(0, str(args.backend.resolve()))
    backend = importlib.import_module("TMBuilder")
    nodes, names = api.parse_dag(api.git_bytes(None, "ZF/m254/coq/prog/Dag254.v").decode())
    _, _, old_contract = api.old_contract(nodes)
    args.output_dir.mkdir(parents=True, exist_ok=True)

    started = time.monotonic()
    baseline_program = api.equality_free_rows(reordered=True, dual=True)
    baseline_builder, baseline = compile_program(
        api, backend, nodes, names, baseline_program,
        "raw_equality_free_C_G_shared_dual_base3")
    baseline_path = args.output_dir / "raw252-baseline.tm"
    baseline_builder.tm.save(str(baseline_path))
    baseline["table_sha256"] = sha(baseline_path)
    baseline["table"] = str(baseline_path.resolve())
    assert baseline["working_states"] == 252
    assert baseline["table_sha256"] == "06feea82f1ea6cbd7a93458d00e76c4afb14ab18e1cade3bb4afe1740dc48cab"
    print("Baseline reproduced: 252 states, expected exact named-table hash.", flush=True)

    fixed_order = (1, 7, 5, 3)
    definitions = {
        "U": "All(c,Rel(c,a)) -> Rel(b,a)",
        "P": "[All(c, Rel(c,a) <-> Rel(c,b))] -> [Rel(a,c) -> Rel(b,c)]",
    }
    controls = {}
    for control, definition in definitions.items():
        records = []
        best = None
        best_builder = None
        best_tree = None
        control_formula = None
        for permutation in itertools.permutations(("C", "G", "V", control)):
            for tree in trees(permutation):
                program, control_formula = make_program(api, control, fixed_order, tree)
                builder, result = compile_program(api, backend, nodes, names, program,
                                                  f"diagnostic_{control}")
                result.update({"phase": "bundle_layout", "rho_order": [9-i for i in fixed_order],
                               "bundle_tree": tree, "bundle": pretty_tree(tree)})
                records.append(result)
                if best is None or result["working_states"] < best["working_states"]:
                    best, best_builder, best_tree = result, builder, tree
            if len(records) % 30 == 0:
                print(f"{control}: {len(records)}/120 layouts; best {best['working_states']} states.", flush=True)
        assert len(records) == 120
        first_best_tree = best_tree
        phase1_best = dict(best)
        for order in itertools.permutations((1, 3, 5, 7)):
            program, _ = make_program(api, control, order, first_best_tree)
            builder, result = compile_program(api, backend, nodes, names, program,
                                              f"diagnostic_{control}")
            result.update({"phase": "logical_order", "rho_order": [9-i for i in order],
                           "bundle_tree": first_best_tree,
                           "bundle": pretty_tree(first_best_tree)})
            records.append(result)
            if result["working_states"] < best["working_states"]:
                best, best_builder, best_tree = result, builder, first_best_tree
        assert len(records) == 144
        table = args.output_dir / f"diagnostic-{control}-best.tm"
        best_builder.tm.save(str(table))
        controls[control] = {
            "definition": definition,
            "formula_AST": control_formula,
            "all_control_instances_have_existing_gate_c_ne_a_b": True,
            "cases": len(records),
            "bundle_layout_cases_at_fixed_rho_order": 120,
            "logical_orders_on_first_best_bundle": 24,
            "not_full_cartesian_search": True,
            "first_phase_best": phase1_best,
            "minimum_working_states_in_this_search": best["working_states"],
            "cost_distribution": dict(sorted(Counter(r["working_states"] for r in records).items())),
            "best_recipe": best,
            "best_table": str(table.resolve()),
            "best_table_sha256": sha(table),
            "minimizers_in_sample": [r for r in records if r["working_states"] == best["working_states"]],
            "records": records,
        }
        print(f"{control} finished: {best['working_states']} states; {best['bundle']}; rho{best['rho_order']}.", flush=True)

    result = {
        "status": "diagnostic_compiler_costs_only",
        "full_first_order_completeness_proved": False,
        "ZFC_calibration_proved": False,
        "literal_TM_simulation_proved": False,
        "new_consistency_machine_bound_claimed": False,
        "raw_countermodel_excluded_by_each_control": True,
        "countermodel_exclusion_witnesses": {
            "U": {"labels": {"a": 1, "b": 2, "c": 0},
                  "assignment": {"0": 0, "1": 5, "2": 0},
                  "control_truth_value": False},
            "P": {"labels": {"a": 0, "b": 1, "c": 2},
                  "assignment": {"0": 1, "1": 1, "2": 4},
                  "control_truth_value": False},
        },
        "raw_countermodel_exclusion_is_not_completeness": True,
        "formula_scale": 3,
        "common_subsequence_extraction_before_binary_lowering": True,
        "GEN_before_cache_read_preserved": True,
        "dual_rho6_relative_falsity_bridge_unproved": True,
        "old_AX_symbolic_contract": old_contract,
        "upstream_commit": api.COMMIT,
        "pinned_backend_and_DAG_sha256": api.SOURCE_SHA256,
        "imported_script_sha256": {name: sha(source / name) for name in (
            "theory_backend_experiment.py", "recover_wade_dag.py", "pairing_backend_experiment.py")},
        "experiment_sha256": sha(__file__),
        "baseline": baseline,
        "controls": controls,
        "control_compilations": sum(c["cases"] for c in controls.values()),
        "total_compilations_including_baseline": 289,
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "named_table_convention": "One tape, binary, blank0, explicit start directive; omitted transition stops; separate terminal halt. No compiler simulation proved.",
    }
    args.results.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"Results: {args.results.resolve()}", flush=True)


if __name__ == "__main__":
    main()
