#!/usr/bin/env python3
"""Check context-independent return effects of the published AX macros.

This reads the pinned Coq DAG as data and does not execute third-party code.
It is an executable certificate for a finite, sound control-effect analysis.
See macro_contract.tex for the mathematical soundness and reassociation proof.
It does not prove the unary-register-to-TM compiler simulation or any theory
calibration, and its implementation has not been formalized in a prover.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re

DAG_SHA256 = "538ddaddd932058c2b319011126579d77783231f54331772377c05848a0599e3"
MACROS = {166: "a", 121: "b", 168: "c", 171: "zero", 177: "one",
          119: "imp", 181: "rel", 182: "eq", 180: "all",
          218: "not", 178: "and", 183: "exists", 176: "read_b",
          158: "read_u", 208: "move_u", 192: "copy_c",
          131: "gate", 211: "restore_c_copy", 197: "a_to_b"}
NORMAL = ("normal", 0)


def read_dag(path):
    data = path.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    if digest != DAG_SHA256:
        raise ValueError("DAG bytes differ from the frozen input")
    pattern = (r"\| ([0-9]+) => \((E\w+(?: [0-9]+)?), (E\w+(?: [0-9]+)?)\)"
               r"\s+\(\* (.*?) \*\)")
    nodes, names = {}, {}
    for number, left, right, name in re.findall(pattern, data.decode()):
        q = int(number)
        if q in nodes:
            raise ValueError("duplicate node")
        nodes[q], names[q] = (left, right), name
    if set(nodes) != set(range(219)):
        raise ValueError("expected the complete 219-node source DAG")
    return nodes, names, digest


def possible_returns(nodes):
    """Conservatively overapproximate terminating exits of each finite tree.

    A continue-1 at a right child restarts its parent, so it adds no terminating
    exit. All other exits are computed structurally, with normal sequencing.
    The number of restarts is irrelevant: any finite terminating execution has
    a final traversal, whose exit is one of the listed alternatives.
    """
    answers, active = {}, set()

    def edge(text):
        words = text.split()
        kind = words[0]
        if kind == "EHalt" and len(words) == 1:
            return frozenset({("halt", 0)})
        if len(words) != 2 or not words[1].isdigit():
            raise ValueError("invalid source edge")
        k = int(words[1])
        if kind == "ENode":
            return node(k)
        if kind == "EInc" and k < 9:
            return frozenset({NORMAL})
        if kind == "EDecnz" and k < 9:
            return frozenset({NORMAL, ("break", 1)})
        if kind == "EBreak" and k > 0:
            return frozenset({("break", k)})
        if kind == "EContinue" and k > 0:
            return frozenset({("continue", k)})
        raise ValueError("unsupported source edge")

    def node(q):
        if q in answers:
            return answers[q]
        if q in active or q not in nodes:
            raise ValueError("cyclic or missing source node")
        active.add(q)
        left, right = (edge(x) for x in nodes[q])
        result = set()
        for kind, k in left:
            if kind == "break":
                result.add(NORMAL if k == 1 else ("break", k - 1))
            elif kind == "normal":
                for kind2, k2 in right:
                    if kind2 == "continue":
                        if k2 != 1:
                            result.add(("continue", k2 - 1))
                    else:
                        result.add((kind2, k2))
            else:
                result.add((kind, k))
        active.remove(q)
        answers[q] = frozenset(result)
        return answers[q]

    for q in nodes:
        node(q)
    return answers


def self_tests():
    # An unguarded decrement exposes a break; grouping it changes behavior.
    # ((dec r0, inc r1), inc r2) and (dec r0, (inc r1, inc r2))
    # at r0=0 produce respectively [0,0,1] and [0,0,0].
    def execute(tree, values):
        if isinstance(tree, str):
            kind, label = tree.split()
            r = int(label)
            if kind == "inc":
                values[r] += 1
                return NORMAL
            if values[r] > 0:
                values[r] -= 1
                return NORMAL
            return "break", 1
        left, right = tree
        result = execute(left, values)
        if result[0] == "break":
            return NORMAL if result[1] == 1 else ("break", result[1] - 1)
        if result == NORMAL:
            return execute(right, values)
        return result
    left_values, right_values = [0, 0, 0], [0, 0, 0]
    execute((("dec 0", "inc 1"), "inc 2"), left_values)
    execute(("dec 0", ("inc 1", "inc 2")), right_values)
    if left_values != [0, 0, 1] or right_values != [0, 0, 0]:
        raise RuntimeError("negative reassociation example changed")
    cases = [
        ({0: ("EInc 0", "EInc 1")}, {NORMAL}),
        ({0: ("EDecnz 0", "EContinue 1")}, {NORMAL}),
        ({0: ("EInc 0", "EBreak 2")}, {("break", 2)}),
        ({0: ("EContinue 2", "EInc 0")}, {("continue", 2)}),
        ({0: ("EInc 0", "EHalt")}, {("halt", 0)}),
        ({0: ("EInc 0", "EContinue 1")}, set()),
    ]
    for graph, expected in cases:
        if possible_returns(graph)[0] != expected:
            raise RuntimeError("control-effect regression")
    for graph in ({0: ("ENode 0", "EInc 0")},
                  {0: ("ENode 1", "EInc 0")},
                  {0: ("EInc 9", "EInc 0")}):
        try:
            possible_returns(graph)
        except ValueError:
            pass
        else:
            raise RuntimeError("invalid control graph accepted")
    return {"cases_passed": len(cases) + 4,
            "unrestricted_reassociation_counterexample": {
                "initial_registers": [0, 0, 0],
                "left_bracketed_final_registers": left_values,
                "right_bracketed_final_registers": right_values}}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--dag", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    nodes, names, digest = read_dag(args.dag)
    old_effects = possible_returns(nodes)
    base3 = dict(nodes)
    if base3[118][0] != "ENode 156":
        raise ValueError("unexpected old multiply-four helper")
    base3[118] = ("ENode 157", base3[118][1])
    new_effects = possible_returns(base3)
    for q in MACROS:
        if old_effects[q] != {NORMAL} or new_effects[q] != {NORMAL}:
            raise ValueError(f"macro {q} can return nonnormally")
    result = {
        "source_dag_sha256": digest,
        "upstream_commit": "297ab8df7e5de329605c3875b4934643b371a5e3",
        "source_nodes": len(nodes),
        "base3_change": {"node": 118, "old_left": 156, "new_left": 157},
        "macros": [{"id": q, "name": MACROS[q], "source_name": names[q],
                    "original_possible_returns": sorted(old_effects[q]),
                    "base3_possible_returns": sorted(new_effects[q])}
                   for q in sorted(MACROS)],
        "all_19_macros_return_only_normally": True,
        "does_not_assert_macro_termination": True,
        "effect_sets_are_upper_bounds_not_exact_semantics": True,
        "self_tests": self_tests(),
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope": "Finite control-effect certificate supporting exact-word reassociation at the structured-register level; no compiler simulation or consistency calibration."}
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "macros"}, indent=2))


if __name__ == "__main__":
    main()
