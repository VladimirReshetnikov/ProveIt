"""Preserve every old-rho6 C/G/V macro while optimizing its shared grammar.

This measures an uncalibrated register program.  It is not a new proved ZFC
consistency machine.  Requires the pinned ProveIt snapshot; no source is edited.
The generated backend and named tables are placed only in --output.
"""
from __future__ import annotations

import argparse
from collections import Counter
from functools import cache
import hashlib
import importlib
import json
from pathlib import Path
import random
import sys
import time

PINNED_HEAD = "96836f9eea3540e96322c3d28c7127a582aae223"


def repair(word, seed, exponent=4):
    """Exact-word Re-Pair with weighted choice of nonoverlapping repeat pairs."""
    rng, seq, grammar = random.Random(seed), list(word), []
    while True:
        counts = Counter(zip(seq, seq[1:]))
        # Equal-token pairs can overlap. Count actual replacements rather than
        # allowing one unlucky overlapping pair to terminate the whole search.
        for pair in list(counts):
            if pair[0] == pair[1]:
                i = n = 0
                while i + 1 < len(seq):
                    if tuple(seq[i:i+2]) == pair:
                        n += 1
                        i += 2
                    else:
                        i += 1
                counts[pair] = n
        choices = [(pair, f) for pair, f in counts.items() if f >= 2]
        if not choices:
            return seq, grammar
        pair = rng.choices([p for p, _ in choices], [f**exponent for _, f in choices])[0]
        new, i = [], 0
        while i < len(seq):
            if i+1 < len(seq) and tuple(seq[i:i+2]) == pair:
                new.append(("g", len(grammar)))
                i += 2
            else:
                new.append(seq[i])
                i += 1
        if len(seq)-len(new) < 2:
            raise ValueError("nonoverlapping repeat count was incorrect")
        grammar.append(pair)
        seq = new


def expansion(builder, q, macros):
    if not isinstance(q, int) or q in macros:
        return [q]
    return [v for child in builder.sequences[q].seq
            for v in expansion(builder, child, macros)]


def build(backend, nodes, names, program, seed, exponent, rwd, tbe):
    builder = rwd.builder_from_dag(backend, nodes, names)
    builder.sequence_lookup = {s.seq: i for i, s in enumerate(builder.sequences)}
    if seed is None:
        tbe.lower_program(builder, nodes, program, "old_rho6_control", shared=True,
                          base3=True)
        return builder, None
    residual, grammar = repair(program, seed, exponent)
    refs = {}
    resolve = lambda x: refs[x] if isinstance(x, tuple) else x
    for i, pair in enumerate(grammar):
        refs["g", i] = builder.add_sequence([resolve(x) for x in pair])
    root = builder.add_sequence([resolve(x) for x in residual])
    builder.sequences[root].name = f"old_rho6_repair_{seed}_{exponent}().0"
    if expansion(builder, root, tbe.MACROS) != program:
        raise ValueError("grammar changed expanded macro word")
    for i, sequence in enumerate(builder.sequences):
        if i != 1:
            sequence.seq = tuple(root if x == 1 else x for x in sequence.seq)
    builder.breakout_common_subsequences()
    builder.reduce_to_cons()
    builder.name_sequences()
    if expansion(builder, root, tbe.MACROS) != program:
        raise ValueError("backend sharing changed expanded macro word")
    if builder.sequences[118].seq[0] != 156:
        raise ValueError("unexpected original formula multiplier")
    builder.sequences[118].seq = (157, builder.sequences[118].seq[1])
    return builder, {"rules": len(grammar), "residual_tokens": len(residual)}


def closed_macro_checks(nodes, macros):
    @cache
    def bounds(edge):
        kind, *payload = edge.split()
        n = int(payload[0]) if payload else 0
        if kind == "ENode":
            left, right = map(bounds, nodes[n])
            return max(left[0]-1, right[0], 0), max(left[1], right[1]-1, 0)
        if kind == "EDecnz":
            return 1, 0
        if kind == "EBreak":
            return n, 0
        if kind == "EContinue":
            return 0, n
        return 0, 0
    result = {q: bounds(f"ENode {q}") for q in macros}
    if any(b != (0, 0) for b in result.values()):
        raise ValueError("macro escapes source sequence control")
    return result


def record(builder, path):
    builder.generate()
    builder.tm.gc()
    states = {q for q, _ in builder.tm.states}
    if path is not None:
        builder.tm.save(str(path))
    return {
        "working_states": len(states),
        "decision_states": sum(not q[0].isdigit() for q in states),
        "framework_states": sum(q[0].isdigit() for q in states),
        "transition_rows": len(builder.tm.states),
        "missing_rows": [[q, bit] for q in sorted(states) for bit in ("0", "1")
                         if (q, bit) not in builder.tm.states],
        **({"named_table_sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
           if path is not None else {}),
    }


def main():
    if not __debug__:
        raise RuntimeError("assertion-disabled execution is not supported")
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--seeds", type=int, default=200)
    ap.add_argument("--start-seed", type=int, default=0)
    ap.add_argument("--exponent", type=int, default=4)
    args = ap.parse_args()
    repo, output = args.repo.resolve(), args.output.resolve()
    if output == repo or repo in output.parents:
        ap.error("--output must be outside the source snapshot")
    output.mkdir(parents=True, exist_ok=True)
    source = repo / "Computability/BusyBeaver/Research/ZFC"
    sys.path.insert(0, str(source))
    import recover_wade_dag as rwd
    import theory_backend_experiment as tbe
    for name in ("TMBuilder.py", "tm.py", "tmdb.py", "LICENSE.wade"):
        (output/name).write_bytes(rwd.git_bytes(None, "ZF/generator/"+name))
    sys.path.insert(0, str(output))
    backend = importlib.import_module("TMBuilder")
    nodes, names = rwd.parse_dag(rwd.git_bytes(None, "ZF/m254/coq/prog/Dag254.v").decode())
    tbe.old_contract(nodes)
    closed = closed_macro_checks(nodes, tbe.MACROS)
    # The published old-rho6 minimum order: rho8,rho2,rho4,rho6 and V AND(C AND G).
    program = tbe.equality_free_rows(dual=False, order=(1, 7, 5, 3),
                                    components=("V", "C", "G"), grouping=1)
    control, _ = build(backend, nodes, names, program, None, args.exponent, rwd, tbe)
    control_record = record(control, output/"old-rho6-control.tm")
    if control_record["working_states"] != 254:
        raise ValueError("pinned old-rho6 control did not reproduce 254 states")
    best, minimizers, costs = None, [], Counter()
    begin = time.monotonic()
    for seed in range(args.start_seed, args.start_seed+args.seeds):
        builder, grammar = build(backend, nodes, names, program, seed, args.exponent, rwd, tbe)
        measurement = record(builder, None)
        cost = measurement["working_states"]
        costs[cost] += 1
        if best is None or cost < best["working_states"]:
            best = dict(measurement)
            path = output/"old-rho6-best.tm"
            builder.tm.save(str(path))
            best.update(seed=seed, exponent=args.exponent, grammar=grammar,
                        named_table_sha256=hashlib.sha256(path.read_bytes()).hexdigest())
            minimizers = [seed]
            print(json.dumps({"new_minimum":cost,"seed":seed,"elapsed":round(time.monotonic()-begin,2)}),flush=True)
        elif cost == best["working_states"]:
            minimizers.append(seed)
    evidence = {
        "pinned_proveit_head": PINNED_HEAD,
        "pinned_upstream_commit": rwd.COMMIT,
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "source_sha256": {name: hashlib.sha256((source/name).read_bytes()).hexdigest()
                          for name in ("recover_wade_dag.py", "theory_backend_experiment.py")},
        "macro_word": program,
        "macro_word_sha256": hashlib.sha256(json.dumps(program,separators=(",",":")).encode()).hexdigest(),
        "macro_word_length": len(program),
        "closed_macro_bounds": closed,
        "logical_order": ["rho8","rho2","rho4","original_rho6"],
        "bundle": "V AND (C AND G)",
        "formula_codec": "Imp=3P; Rel=3P+1; All=3P+2",
        "baseline": control_record,
        "search": {"seed_start":args.start_seed,"seeds":args.seeds,"exponent":args.exponent,
                   "cost_distribution":dict(sorted(costs.items())),"minimizers":minimizers},
        "best": best,
        "all_expanded_macro_words_exact": True,
        "original_rho6_retained": True,
        "proof_and_stack_pairing_unchanged": True,
        "theory_calibration_proved": False,
        "compiler_simulation_proved": False,
        "new_ZFC_machine_or_state_bound_claimed": False,
    }
    (output/"old-rho6-grammar-results.json").write_text(json.dumps(evidence,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"distribution":dict(costs),"best":best}),flush=True)


if __name__ == "__main__":
    main()
