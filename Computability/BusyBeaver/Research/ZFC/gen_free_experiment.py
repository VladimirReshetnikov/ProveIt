#!/usr/bin/env python3
"""Cost GEN elimination by prefix-closing the full primitive axiom families.

This is an ordinary admissibility argument and a complete-control compiler
experiment, not a new Lean calculus/runtime or blank-tape consistency theorem.
The original equality, all logical schemas, gated CP/GIC/vacuity bundle,
MP/DROP/NIP and scheduler are retained. Generated artifacts stay in scratch.
"""
from __future__ import annotations

import argparse
from collections import Counter
import copy
import hashlib
import importlib
import json
from pathlib import Path
import sys
import time

import recover_wade_dag as recover
from full_grammar_experiment import expand, safe_repair
from pairing_backend_experiment import execute_helper
from register_lifetime_experiment import compile_measure, macro_word
import theory_backend_experiment as theory


def prefix_wrapper(backend, nodes, names):
    builder = recover.builder_from_dag(backend, nodes, names)
    builder.sequence_lookup = {s.seq: i for i, s in enumerate(builder.sequences)}
    x = builder.reg("scratch1")
    # Read a Cantor-coded prefix entry. Zero ends; a+1 wraps current in All(a,-).
    # pair162 consumes X,T into Y;117 moves4Y into T;159 adds All tag2.
    wrapper = builder.add_sequence(builder.label("wrap",
        [158, [x.decnz, [[162, [117, 159]], "continue_wrap"]]]))
    builder.sequences[wrapper].name = "axiom_prefix().0"
    builder.reduce_to_cons(); builder.name_sequences()
    return builder, wrapper


def layouts(nodes, wrapper):
    word, _, contract = theory.old_contract(nodes)
    stack, _ = theory.symbolic(word[:-5])
    cuts, last = [], 0
    for k in range(1, len(stack)):
        choices = [i for i in range(last + 1, len(word) - 4)
                   if theory.symbolic(word[:i])[0] == stack[:k + 1]]
        if not choices:
            raise ValueError("missing exact completed-row boundary")
        last = min(choices); cuts.append(last)
    assert len(cuts) == 10 and cuts[0] == 3
    parts, last = [], 0
    for cut in cuts:
        parts.append(word[last:cut]); last = cut
    # GEN is replaced by prefix-closed truth0; all8 original logical rows remain.
    ungrouped = [171, wrapper]
    for part in parts[1:]:
        ungrouped += part + [wrapper]
    ungrouped += theory.TAIL
    # rho8 +rho6 supply MP-only classical propositional logic before projection.
    grouped = parts[1] + [wrapper] + parts[3] + [wrapper] + parts[2]
    for k in (4, 5, 6, 7, 8):
        grouped += parts[k] + [178]
    # Apply the literal bundle gates before inserting it into the conjunction.
    grouped += parts[9] + theory.TAIL + [178, wrapper]
    # rho8(0,0,0,0)=0, so the grouped variant also supplies truth's every prefix.
    assert word == sum(parts, []) + theory.TAIL
    return dict(ungrouped=ungrouped, grouped=grouped), cuts, contract


def wrapper_tests(builder, wrapper):
    P = lambda a, b: (a + b) * (a + b + 1) // 2 + b
    def pack(items, tail):
        for item in reversed(items):
            tail = P(item, tail)
        return tail
    cases = 0
    for top in range(8):
        for prefix in ([], [0], [1], [0, 1], [2, 0]):
            tail = 0 if len(prefix) > 1 else 3
            pl = pack([a + 1 for a in prefix] + [0], tail)
            actual = [7, top, 11, 13, 17, 23, 0, 0, pl]
            expected = actual[:]
            for a in prefix:
                expected[1] = 4 * P(a, expected[1]) + 2
            expected[8] = tail
            if execute_helper(builder, wrapper, actual, fuel=10_000_000) != ("normal",) or actual != expected:
                raise ValueError((top, prefix, actual, expected))
            cases += 1
    return cases


def compile_layout(backend, helper, nodes, program, wrapper, directory, seeds):
    # Reuse only exact original subwords; wrappers are barriers to such reuse.
    b = copy.deepcopy(helper)
    root = b.add_sequence(theory.reuse_published_subsequences(nodes, program))
    b.sequences[1].seq = b.sequences[root].seq
    b.reduce_to_cons(); b.name_sequences()
    boundary = set(theory.MACROS) | {wrapper}
    assert macro_word(b, 1, boundary) == program
    unshared = compile_measure(backend, b, "original-nine", directory / "unshared")
    # Separate terminals from Re-Pair's reserved300+i grammar variables.
    vocab = sorted(set(program)); assert len(vocab) < 300
    ids = {value: i for i, value in enumerate(vocab)}
    compact = [ids[value] for value in program]
    best_key, best_builder, histogram, records = None, None, Counter(), []
    for seed in range(seeds):
        b = copy.deepcopy(helper)
        residual, productions, _ = safe_repair(compact, seed, 2)
        assert expand(residual, productions) == compact
        nonterminals = {}
        def token(value):
            return nonterminals[value] if value >= 300 else vocab[value]
        for i, pair in enumerate(productions):
            nonterminals[300 + i] = b.add_sequence([token(v) for v in pair])
        root = b.add_sequence([token(v) for v in residual])
        b.sequences[1].seq = b.sequences[root].seq
        b.reduce_to_cons(); b.name_sequences()
        assert macro_word(b, 1, boundary) == program
        result = compile_measure(backend, b, "original-nine", None)
        result["seed"] = seed
        records.append(result); histogram[result["total_states"]] += 1
        key = result["total_states"], result["decision_states"], seed
        if best_key is None or key < best_key:
            best_key, best_builder = key, b
    best = compile_measure(backend, best_builder, "original-nine", directory / "best")
    best["seed"] = best_key[2]
    return dict(unshared=unshared, best=best, histogram=dict(histogram),
                every_AX_macro_expansion_checked=True, candidates=records,
                expanded_word=program, word_length=len(program))


def main():
    if not __debug__:
        raise RuntimeError("Run without -O; inherited checks use assertions")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scratch", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--seeds", type=int, default=32)
    args = parser.parse_args()
    work = args.scratch.resolve()
    if work == recover.ROOT or recover.ROOT in work.parents or work == Path("/"):
        parser.error("scratch must be outside the checkout")
    if not 1 <= args.seeds <= 64:
        parser.error("bounded probe requires1..64 seeds")
    work.mkdir(parents=True, exist_ok=True)
    backend_dir = work / "backend"; backend_dir.mkdir(exist_ok=True)
    for name in ("TMBuilder.py", "tm.py", "tmdb.py", "LICENSE.wade"):
        (backend_dir / name).write_bytes(recover.git_bytes(None, "ZF/generator/" + name))
    sys.path.insert(0, str(backend_dir))
    backend = importlib.import_module("TMBuilder")
    raw = recover.git_bytes(None, "ZF/m254/coq/prog/Dag254.v")
    nodes, names = recover.parse_dag(raw.decode())
    start = time.monotonic()
    original = recover.builder_from_dag(backend, nodes, names)
    baseline = compile_measure(backend, original, "original-nine", work / "original")
    no_gen = copy.deepcopy(original)
    no_gen.sequences[1].seq = no_gen.sequences[2].seq
    deletion = compile_measure(backend, no_gen, "original-nine", None)
    helper, wrapper = prefix_wrapper(backend, nodes, names)
    programs, cuts, contract = layouts(nodes, wrapper)
    checks = wrapper_tests(helper, wrapper)
    result = dict(upstream_commit=recover.COMMIT,
        attribution="Mira-Cult program; Jeff verification; Wade compiler; repository overlap-safe Re-Pair",
        driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        original=baseline, GEN_deletion_only_incomplete_control=deletion,
        row_boundary_cuts=cuts, source_symbolic_contract=contract,
        prefix_wrapper_register_cases=checks, wrapper_node=wrapper,
        variants={})
    for name, program in programs.items():
        directory = work / name; directory.mkdir(exist_ok=True)
        result["variants"][name] = compile_layout(backend, helper, nodes, program,
                                                  wrapper, directory, args.seeds)
        print(name, result["variants"][name]["best"]["total_states"], flush=True)
    result.update(elapsed_seconds=time.monotonic() - start, seeds=args.seeds,
        original_formula_codec_retained=True, native_equality_rows_retained=True,
        original_gated_theory_bundle_retained=True, numerical_GEN_rule_present=False,
        ordinary_GEN_admissibility_argument="gen_free.md",
        Lean_calculus_or_runtime_theorem_supplied=False,
        candidate_schedule_coverage_formalized=False,
        new_blank_tape_consistency_machine_claimed=False,
        initial_wide_wrapper_grid="not completed:10,000,000-structured-step fuel exhausted; not counted")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
