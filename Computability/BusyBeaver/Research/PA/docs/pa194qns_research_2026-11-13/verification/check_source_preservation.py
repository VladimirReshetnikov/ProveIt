#!/usr/bin/env python3
"""Independent exact source splice audit for QN -> QNS or Q-push -> QS.

This program imports neither a builder nor a symbolic physical runtime.
The all-natural proof is in source_preservation.tex.  The finite replay here
checks the literal instruction binding and the closed-form clock calculations;
it is not presented as a proof by testing unbounded counter values.
"""

import argparse
import hashlib
import json
from pathlib import Path


def read_source(path):
    raw = path.read_bytes()
    code = json.loads(raw)
    for i in code:
        assert i[0] in ("inc", "dec", "jump", "halt")
        if i[0] in ("inc", "dec"):
            assert 0 <= i[1] < 9
        for n in successors(i):
            assert 0 <= n < len(code)
    return code, hashlib.sha256(raw).hexdigest()


def successors(ins):
    if ins[0] in ("inc", "dec"):
        return ins[2:]
    if ins[0] == "jump":
        return ins[1:]
    return []


def edges(code):
    return [(s, t) for s, i in enumerate(code) for t in successors(i)]


def run(code, pc, registers, stops, fuel=100000):
    r = list(registers)
    for clock in range(fuel):
        if pc in stops:
            return pc, r, clock
        ins = code[pc]
        op = ins[0]
        if op == "inc":
            r[ins[1]] += 1
            pc = ins[2]
        elif op == "dec":
            if r[ins[1]]:
                r[ins[1]] -= 1
                pc = ins[3]
            else:
                pc = ins[2]
        elif op == "jump":
            pc = ins[1]
        else:
            return "halt", r, clock
    raise AssertionError("finite diagnostic exhausted its stated fuel")


def comparator_clock(h, x):
    if h == x:
        return 3 * h + 2
    if h > x:
        return 2 * h + x + 4
    return 3 * x + 2


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("parent", type=Path)
    ap.add_argument("candidate", type=Path)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    old, old_sha = read_source(args.parent)
    new, new_sha = read_source(args.candidate)
    assert (len(old), len(new)) in ((3654, 3651), (3673, 3670))
    entry = len(new) - 9
    splice = entry + 7
    assert old[:splice] == new[:splice]

    comparator = [
        ["dec", 5, 4, 1], ["dec", 6, 3, 2], ["jump", 0],
        ["jump", 5], ["dec", 6, 10, 5], ["dec", 5, 7, 6],
        ["jump", 5], ["dec", 6, 9, 8], ["jump", 5],
        ["jump", 11], ["halt"],
    ]
    assert old[:11] == new[:11] == comparator
    assert old[entry:splice] == new[entry:splice] == [
        ["dec", 1, entry+3, entry+1], ["inc", 6, entry+2], ["jump", entry],
        ["dec", 5, splice, entry+4], ["inc", 1, entry+5],
        ["inc", 6, entry+6], ["jump", entry+3],
    ]
    assert old[splice:] == [
        ["dec", 6, splice+3, splice+1], ["inc", 5, splice+2],
        ["jump", splice], ["inc", 6, splice+4], ["jump", 0],
    ]
    assert new[splice:] == [["inc", 5, splice+1], ["jump", 0]]
    for name, code, last in (("parent", old, len(old)-1), ("candidate", new, len(new)-1)):
        e = edges(code)
        assert [(s, t) for s, t in e if s < entry <= t] == [(48, entry)]
        assert [(s, t) for s, t in e if s >= 11 and t < 11] == [(last, 0)]
        assert [(s, t) for s, t in e if s >= entry and t < entry] == [(last, 0)]
        assert [(s, t) for s, t in e if s < 11 and t >= 11] == [(9, 11)]
    assert all(i[0] != "halt" for i in old[11:] + new[11:])

    # Independent finite diagnostics of the displayed inductive clock formulas.
    comparator_probes = 0
    for h in range(33):
        for x in range(33):
            r = [13, 17, 19, 23, 29, h, x, 31, 37]
            pc, out, clock = run(new, 0, r, {10, 11})
            assert clock == comparator_clock(h, x)
            assert pc == (10 if h == x else 11)
            assert out[5] == out[6] == 0
            assert all(out[j] == r[j] for j in range(9) if j not in (5, 6))
            comparator_probes += 1
    source_probes = 0
    for t in range(17):
        for h in range(17):
            for x in range(17):
                r = [13, t, 19, 23, 29, h, x, 31, 37]
                k = t + h + x
                a = run(old, entry, r, {10, 11})
                b = run(new, entry, r, {10, 11})
                assert a[:2] == b[:2]
                assert a[0] == (10 if k == 1 else 11)
                assert a[1][1] == h and a[1][5] == a[1][6] == 0
                assert all(a[1][j] == r[j] for j in range(9) if j not in (1, 5, 6))
                common = 3 * t + 4 * h + 2
                assert a[2] == common + 3 * k + 3 + comparator_clock(k, 1)
                assert b[2] == common + 2 + comparator_clock(1, k)
                assert a[2] - b[2] == (0 if k == 0 else 4 if k == 1 else 2 * k + 4)
                source_probes += 1
    receipt = {
        "parent_instructions_sha256": old_sha,
        "candidate_instructions_sha256": new_sha,
        "parent_sites": len(old),
        "candidate_sites": len(new),
        "identical_prefix_sites": splice,
        "changed_complete_block_entry": entry,
        "only_external_entry": [48, entry],
        "shared_normal_exit": 11,
        "shared_halt_site": 10,
        "literal_block_bindings_pass": True,
        "all_natural_theorem": "source_preservation.tex, induction on natural counter lengths",
        "finite_clock_diagnostics": {
            "comparator_counter_range": [0, 32], "cases": comparator_probes,
            "block_counter_range": [0, 16], "block_cases": source_probes,
        },
        "new_logical_axioms": False,
        "new_lean_or_rocq_verification": False,
        "scope": "Exact source binding plus a written all-natural proof; finite probes are diagnostics only.",
    }
    out = json.dumps(receipt, indent=2) + "\n"
    if args.output:
        args.output.write_text(out)
    print(out, end="")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Assertions must be enabled; do not run with -O.")
    main()
