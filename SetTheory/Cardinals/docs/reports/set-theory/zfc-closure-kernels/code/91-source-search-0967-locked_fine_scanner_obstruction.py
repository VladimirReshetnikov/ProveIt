#!/usr/bin/env python3
"""Check the locked zero-six path in the current finer-token search family.

The word dictionary may cross original macro boundaries. The 44 original
atomic implementations and the 54 exact bootstrap projection equations remain
fixed. An AX source override is permitted because the witness does not enter AX.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("fine", type=Path)
    p.add_argument("--candidate", type=Path)
    p.add_argument("--output", type=Path)
    a = p.parse_args()
    sys.path.insert(0, str(a.fine.resolve() / "runtime/code"))
    import audit_fine_grammar as audit
    override = json.loads(a.candidate.read_text()).get("source_override") if a.candidate else None
    source, terminals, names, allowed, encode = audit.make_vocabulary(override)
    by_ast = {int(ast): names[int(q)] for q, ast in source["sequence_ast_roots"].items()}
    seq_state = {int(ast): int(q) for q, ast in source["sequence_ast_roots"].items()}
    lock_path = audit.BASE / "inputs/state_reduction/bootstrap-lock54.txt"
    lines = lock_path.read_text().splitlines()
    assert len(lines) == int(lines[0]) + 1 == 55
    locks = {(encode(w), b): encode(t) for w, b, t in map(str.split, lines[1:])}
    assert len(locks) == 54
    path = "1111000000"
    state = ("ast", source["original_ast"])
    trace, sequence_entries, atomic_entries = [], [], []
    for bit in path:
        while True:
            kind, value = state
            if kind == "ast" and value in by_ast:
                sequence_entries.append(seq_state[value])
                state = ("word", by_ast[value])
                continue
            if kind == "word" and value in terminals:
                atomic_entries.append(terminals[value])
                state = ("ast", source["atoms"][terminals[value]]["ast"])
                continue
            break
        before = list(state)
        if state[0] == "word":
            assert (state[1], bit) in locks
            state = ("word", locks[state[1], bit])
            premise = "fine-token bootstrap projection"
        else:
            row = source["ast_dag"][state[1]]
            assert row[0] == "N"
            state = ("ast", row[1 + int(bit)])
            premise = "immutable atomic AST"
        trace.append(dict(before=before, bit=int(bit), after=list(state), premise=premise))
    assert state[0] == "ast" and source["ast_dag"][state[1]] == ["L", ["dec", 1]]
    assert 76 not in sequence_entries
    report = dict(status="PASS_EXACT_FINE_FAMILY_OBSTRUCTION", forced_path=path,
                  forced_zero_run=6, forced_leaf=["dec", 1], mutable_rules_consulted=0,
                  sequence_entries=sequence_entries, atomic_entries=atomic_entries,
                  overridden_AX_entered=False, candidate=str(a.candidate) if a.candidate else None,
                  bootstrap_lock_sha256=hashlib.sha256(lock_path.read_bytes()).hexdigest(),
                  trace=trace,
                  scope="Applies to the present 44 fixed atomic implementations and all54 exact projection locks, including arbitrary transparent fine-token resegmentation and AX-only source replacement. It does not constrain a different bootstrap, atomic implementation, or scanner invariant.")
    out = json.dumps(report, indent=2) + "\n"
    if a.output:
        a.output.write_text(out)
    print(out, end="")


if __name__ == "__main__":
    main()
