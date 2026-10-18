"""Measure complete source controls with independently oriented atomic codecs.

This is a compiler measurement, not a new TM/ZFC correctness endpoint.
The unchanged pinned Wade backend and the ProveIt Re-Pair helpers are credited
in the generated evidence. All generated files stay outside the source clone.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import importlib
import itertools
import json
from pathlib import Path
import subprocess
import sys
import time

BASE = Path(__file__).resolve().parent
repo_parser = argparse.ArgumentParser(add_help=False)
repo_parser.add_argument("--repo", type=Path, default=BASE.parent / "ProveIt")
repo_args, _ = repo_parser.parse_known_args()
REPO = repo_args.repo.resolve()
PIN = "e58338db7545909907e07a7603e8eb88625c527a"
RESEARCH = REPO / "Computability/BusyBeaver/Research/ZFC"
sys.dont_write_bytecode = True
sys.path.insert(0, str(RESEARCH))
import recover_wade_dag as recover
import theory_backend_experiment as theory
import full_grammar_experiment as common
import layout_grammar_experiment as layout


def atom_orientation(formula, kinds):
    if not isinstance(formula, tuple):
        return formula
    kind, a, b = formula
    a, b = atom_orientation(a, kinds), atom_orientation(b, kinds)
    return (kind, b, a) if kind in kinds else (kind, a, b)


def selected_formula():
    source19 = common.load_file("orientation_source19_layout", common.REPORT /
        "code/19-subst-engineering-full_logic_search.py")
    spec, _ = theory.published_spec()
    rows = spec["ax_rows"]("a", "h", "b", "c", "u")
    c = source19.variants(spec["bundle_C"]("a", "b", "c"), theory)[2]
    g = source19.variants(spec["bundle_G"]("a", "b", "c"), theory)[1]
    vacuity = [theory.Imp(rel("a", "b"), theory.All("c", rel("a", "b")))
                for rel in (theory.Rel, theory.Eq)]
    order = list(itertools.permutations(range(4)))[16]
    factors = [c, g, *vacuity]
    bundle = source19.trees([factors[i] for i in order], theory)[1]
    return rows, bundle


def setup(out):
    snapshot = out / "snapshot"
    backend_path = out / "backend"
    backend_path.mkdir(parents=True, exist_ok=True)
    paths = list(recover.SOURCE_SHA256) + ["ZF/m254/tools/logic/spec.py"]
    identities = {}
    dependencies = [
        RESEARCH / name for name in (
            "recover_wade_dag.py", "theory_backend_experiment.py",
            "pairing_backend_experiment.py", "full_grammar_experiment.py",
            "layout_grammar_experiment.py")]
    dependencies += [common.REPORT / name for name in (
        "code/08-schema-machine-rebracket_axioms.py",
        "code/19-subst-engineering-full_logic_search.py",
        "data/19-subst-engineering-artifacts-full_logic_results.json")]
    for target in dependencies:
        relative = str(target.relative_to(REPO))
        original = subprocess.check_output(["git", "show", f"{PIN}:{relative}"], cwd=REPO)
        assert target.read_bytes() == original, f"working source differs from pin: {relative}"
        identities[relative] = hashlib.sha256(original).hexdigest()
    for p in paths:
        data = subprocess.check_output(["git", "show", f"{PIN}:lib/jeff-busy-beaver-zfc254/{p}"], cwd=REPO)
        target = snapshot / p
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        identities[p] = hashlib.sha256(data).hexdigest()
        if p in recover.SOURCE_SHA256:
            assert identities[p] == recover.SOURCE_SHA256[p]
        if p.startswith("ZF/generator/"):
            (backend_path / Path(p).name).write_bytes(data)
    recover.SNAPSHOT = theory.SNAPSHOT = snapshot
    sys.path.insert(0, str(backend_path))
    return importlib.import_module("TMBuilder"), identities


def main():
    if not __debug__:
        raise RuntimeError("Run without -O: source checks use assertions")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=REPO)
    parser.add_argument("--seeds", type=int, default=256)
    parser.add_argument("--out", type=Path, default=BASE / "orientation_results")
    args = parser.parse_args()
    out = args.out.resolve()
    assert not (out == REPO or REPO in out.parents)
    out.mkdir(parents=True, exist_ok=True)
    backend, identities = setup(out)
    nodes, names = recover.parse_dag(recover.git_bytes(None, "ZF/m254/coq/prog/Dag254.v").decode())
    helper = common.load_file("orientation_repair", common.REPORT / "code/08-schema-machine-rebracket_axioms.py")
    rows, bundle = selected_formula()
    baseline_word, _ = layout.selected_word(nodes)
    results = []
    start = time.monotonic()
    framework_checks = {}
    old_framework_leaves = layout.framework_leaves(nodes)
    for kinds in [(), ("rel",), ("eq",), ("rel", "eq")]:
        oriented_rows = [atom_orientation(row, kinds) for row in rows]
        oriented_bundle = atom_orientation(bundle, kinds)
        word = ([166, 121, 180, 176] +
            [q for row in oriented_rows[1:] for q in theory.emit(row)] +
            theory.emit(oriented_bundle) + theory.TAIL)
        actual, events = theory.symbolic(word)
        assert actual == ["old_top", *oriented_rows, oriented_bundle]
        assert atom_orientation(atom_orientation(bundle, kinds), kinds) == bundle
        if not kinds:
            assert word == baseline_word
        token_words = layout.tokenizations(nodes, word)
        minimum = None
        histogram = Counter()
        for lane, token_word in token_words.items():
            for exponent in (2, 4, 8):
                for seed in range(args.seeds):
                    seq, grammar = helper.repair(token_word, seed, exponent)
                    assert common.expand(seq, grammar) == token_word
                    nn, nm, root = layout.transform(nodes, names, token_word, seq, grammar)
                    assert layout.framework_leaves(nn) == old_framework_leaves
                    depth = layout.dispatch_depth(nn)
                    cost = len(nn) + 55 + depth
                    if depth not in framework_checks:
                        control = helper.compile_dag(backend, nn, nm)
                        helper.reextract(control, nn, nm)
                        control_states = {q for q, _ in control.states}
                        framework_count = sum(q[0].isdigit() for q in control_states)
                        assert len(control_states) == cost
                        assert framework_count == 55 + depth
                        framework_checks[depth] = dict(decision_nodes=len(nn),
                            framework_states=framework_count,
                            total_states=len(control_states), every_edge_reextracted=True)
                    histogram[cost] += 1
                    key = (cost, len(nn), lane, exponent, seed)
                    if minimum is None or key < minimum["key"]:
                        minimum = dict(key=key, nodes=nn, names=nm, root=root, word=word,
                            lane=lane, exponent=exponent, seed=seed, residual=seq, grammar=grammar)
        machine = helper.compile_dag(backend, minimum["nodes"], minimum["names"])
        helper.reextract(machine, minimum["nodes"], minimum["names"])
        table, labels, missing = common.normalize(machine)
        states = {q for q, _ in machine.states}
        assert len(states) == minimum["key"][0]
        lane_name = "-".join(kinds) if kinds else "native"
        lane_out = out / lane_name
        lane_out.mkdir(exist_ok=True)
        (lane_out / "candidate.tm").write_bytes(table)
        common.write_json(lane_out / "labels.json", labels)
        common.write_json(lane_out / "dag.json", dict(root=0, nodes=minimum["nodes"], names=minimum["names"]))
        common.write_json(lane_out / "recipe.json", {k:minimum[k] for k in ("word","lane","exponent","seed","residual","grammar")})
        item = dict(orientation=kinds, working_states=len(states), decision_nodes=len(minimum["nodes"]),
            framework_states=len(states)-len(minimum["nodes"]), table_sha256=hashlib.sha256(table).hexdigest(),
            macro_count=len(word), trials=sum(histogram.values()), histogram=dict(sorted(histogram.items())),
            winner={k:minimum[k] for k in ("lane","exponent","seed")}, events=events,
            symbolic_stack_exact=True, every_compiled_edge_reextracted=True,
            binary_runtime_proved=False, source_calibration_proved=False)
        results.append(item)
        print(json.dumps(item), flush=True)
    common.write_json(out / "evidence.json", dict(pin=PIN, source_sha256=identities, results=results,
        framework_cost="55 fixed states plus actual consecutive-zero dispatcher depth",
        framework_checks=framework_checks, all_framework_leaf_sets_preserved=True,
        elapsed_seconds=time.monotonic()-start, driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()))


if __name__ == "__main__":
    main()
