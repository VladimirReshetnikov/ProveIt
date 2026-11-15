#!/usr/bin/env python3
"""Rebuild and replay the above-target H5XD research machine.

This uses the inherited construction-side symbolic checker, with its
arithmetic-box lemmas. It is not an independent literal interpreter or a
proof-assistant kernel check. Default execution replays all 4,786 outcomes.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "code/vendor"))
import compiler as c
import support as s

INC = ("leaf", "inc", 1)
EXPECTED = "b047b473563f92c690441bc77956464b31b146eac7015ead68aa511d77d99bf1"


def tuples(x):
    if isinstance(x, list):
        return tuple(map(tuples, x))
    if isinstance(x, dict):
        return {k: tuples(v) for k, v in x.items()}
    return x


def normalize(t):
    if t == "node60":
        return INC, INC
    if t == "node61":
        return (INC, INC), (INC, INC)
    return tuple(map(normalize, t)) if c.isnode(t) else t


def word(t):
    return word(t[0]) + word(t[1]) if c.isnode(t) else [t]


def substitute(t, w):
    stream = iter(w)

    def rec(t):
        return tuple(map(rec, t)) if c.isnode(t) else next(stream)

    out = rec(t)
    assert next(stream, None) is None
    return out


def rebuild(output, full):
    assert __debug__, "Assertions are required; do not use python -O"
    started = time.monotonic()
    inputs = ROOT / "inputs/reconstruction195"
    frozen = ROOT / "candidate195"
    rows = s.read_table(inputs / "base.raw.native.tm")
    nodes = tuples(json.loads((inputs / "base.nodes.json").read_text()))
    c.machine = lambda: (rows, [])
    c.raw_nodes = lambda: nodes
    c.MACROS[(INC, INC)] = 99
    c.MACROS[((INC, INC), (INC, INC))] = 190

    inherited = normalize(tuples(json.loads((inputs / "witness_H5X.tree.json").read_text())))
    emitted = word(inherited)
    assert len(emitted) == 189 and emitted[120:123] == ["node70"] * 3
    emitted[120:123] = ["node55"] * 3
    reference = substitute(inherited, emitted)
    tree = normalize(c.read_grammar(frozen / "grammar.json"))
    assert word(tree) == emitted
    raw, _, shape = c.build(tree)
    assert len(raw) // 2 == 203 and len(shape) == 69
    folds = json.loads((frozen / "folds.json").read_text())
    assert len(folds) == 8
    child, aliases = s.apply_folds(raw, folds)
    local = s.check_local_folds(raw, child, aliases, folds)
    assert len(local["cases"]) == 32
    sites, instructions, contracts = c.source(tree)
    _, reference_instructions, _ = c.source(reference)
    assert instructions == reference_instructions
    assert len(sites) == 3677 and len(contracts) == 4786
    assert all(child[q, bit] == rows[q, bit] for q in c.BOXSTATES for bit in (0, 1))
    startup = s.startup(child, sites[25][0])
    assert startup["steps"] == 57922
    dense, labels = s.dense_table(child, 195)
    digest = hashlib.sha256(s.table_text(dense).encode()).hexdigest()
    assert digest == EXPECTED
    for filename, table in (("machine.tm", dense), ("machine.native.tm", child), ("raw.native.tm", raw)):
        assert s.table_text(table) == (frozen / filename).read_text()
    for filename, value in (("labels.json", labels), ("source.instructions.json", instructions),
                            ("sites.json", [["".join(map(str, path)), op, arg] for path, op, arg in sites]),
                            ("local_cases.json", local)):
        assert json.loads(json.dumps(value)) == json.loads((frozen / filename).read_text())
    physical = c.validate(child, contracts) if full else None
    assert not full or physical["ok"], physical
    receipt = {
        "status": "PASS", "states": 195, "raw_states": 203, "readers": 69,
        "folds": 8, "source_sites": 3677, "contracts": 4786,
        "physical": physical, "startup": startup, "sha256": digest,
        "elapsed": time.monotonic() - started,
        "scope": "Above-target research candidate; inherited construction-side symbolic checker; no independent literal replay or kernel proof."
    }
    if output:
        output.mkdir(parents=True, exist_ok=True)
        (output / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
        for filename, table in (("machine.tm", dense), ("machine.native.tm", child), ("raw.native.tm", raw)):
            (output / filename).write_text(s.table_text(table))
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", type=Path)
    p.add_argument("--quick", action="store_true", help="Skip the construction-symbolic instruction replay")
    args = p.parse_args()
    rebuild(args.output, not args.quick)
