#!/usr/bin/env python3
"""Check an exact zero-run obstruction for the frozen-bootstrap grammar family.

This is a finite derivation from the source AST and required projections, not
an exhaustive search and not a lower bound on unrestricted Turing machines.
"""
import argparse
import hashlib
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    base = args.package
    source_path = base / "inputs/closed-sequence-grammar-next22.json"
    symbol_path = base / "inputs/semantic-symbols.json"
    lock_path = base / "inputs/state_reduction/bootstrap-lock54.txt"
    source = json.loads(source_path.read_text())
    symbols = json.loads(symbol_path.read_text())
    encode = {v: k for k, v in symbols.items()}
    by_ast = {
        int(ast): "".join(encode[t] for t in source["flattened_semantic_words"][q])
        for q, ast in source["sequence_ast_roots"].items()
    }
    lines = lock_path.read_text().splitlines()
    assert len(lines) == int(lines[0]) + 1 == 55
    locks = {}
    for row in lines[1:]:
        word, bit, child = row.split()
        assert (word, bit) not in locks
        locks[word, bit] = child

    # For every grammar meeting the lock equations, the following path can be
    # read without consulting even one mutable rule. Named-word steps use a
    # lock; the remaining steps use literal immutable AST nodes.
    path = "1111000000"
    state = ("ast", source["original_ast"])
    trace = []
    for bit in path:
        while True:
            kind, value = state
            if kind == "ast" and value in by_ast:
                state = ("word", by_ast[value])
                continue
            if kind == "word" and len(value) == 1:
                state = ("ast", source["atoms"][symbols[value]]["ast"])
                continue
            break
        before = list(state)
        if state[0] == "word":
            word = state[1]
            assert (word, bit) in locks, (word, bit)
            state = ("word", locks[word, bit])
            premise = "bootstrap projection"
        else:
            row = source["ast_dag"][state[1]]
            assert row[0] == "N"
            state = ("ast", row[1 + int(bit)])
            premise = "immutable source AST"
        trace.append({"from": before, "bit": int(bit), "to": list(state), "premise": premise})
    assert state[0] == "ast"
    leaf = source["ast_dag"][state[1]]
    assert leaf == ["L", ["dec", 1]]
    assert max(map(len, path.split("1"))) == 6
    output = {
        "status": "PASS_EXACT_RESTRICTED_FAMILY_OBSTRUCTION",
        "forced_path": path,
        "forced_leaf": leaf,
        "forced_zero_run": 6,
        "mutable_grammar_rules_consulted": 0,
        "source_sha256": hashlib.sha256(source_path.read_bytes()).hexdigest(),
        "symbols_sha256": hashlib.sha256(symbol_path.read_bytes()).hexdigest(),
        "bootstrap_lock_sha256": hashlib.sha256(lock_path.read_bytes()).hexdigest(),
        "trace": trace,
        "conclusion": "No grammar retaining this semantic vocabulary, source AST outside named sequences, and all 54 bootstrap projections can have maximum source zero-run at most 5.",
        "scope": "This rules out the zero-5 sufficient-condition route with all locks retained. It does not rule out a different bootstrap, a different scanner invariant, semantic resegmentation, or any smaller Turing machine.",
    }
    text = json.dumps(output, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
