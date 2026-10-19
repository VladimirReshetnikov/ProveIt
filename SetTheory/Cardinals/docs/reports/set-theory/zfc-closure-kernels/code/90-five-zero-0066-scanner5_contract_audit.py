#!/usr/bin/env python3
"""Audit the three-zero local contraction premise on all 8,391 source cases."""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import importlib
import json
import sys
import time

sys.dont_write_bytecode = True


def run(reference):
    table_path = reference / "certificate/machine_old.tm"
    assert hashlib.sha256(table_path.read_bytes()).hexdigest() == "f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267"
    sys.path.insert(0, str(reference / "code"))
    f = importlib.import_module("full_symbolic_parametric")
    f.m.TABLE = f.rebuild.read_table(table_path)[0]
    f.m.prove_blocks()
    f.m.prove_word_identity()
    native, current, violations, calls = f.step, {}, [], 0

    def watch(conf, cost, motion, trace):
        nonlocal calls
        f.normalize(conf)
        if conf.state == 41:
            source = conf.right if conf.side == "R" else conf.left
            if isinstance(source[0], f.Run) and source[0].bit == 0:
                calls += 1
                good = conf.side == "L" and source[0].length.c >= 3
                if not good:
                    violations.append(dict(current, side=conf.side,
                                           first_run=str(source[0].length),
                                           prefix=str(source[:6])))
        return native(conf, cost, motion, trace)

    f.step = watch
    sites = json.loads((reference / "certificate/sites_logical.json").read_text())
    began, cases = time.monotonic(), 0
    try:
        for index, (pc, op, register) in enumerate(sites):
            for zero in ([True, False] if op == "CD" else [None]):
                current.update(index=index, pc=pc, op=op, r=register, zero=zero)
                f.case(pc, op, register, zero, [[0, 9]] * 9)
                cases += 1
                if cases % 1000 == 0:
                    print(f"Audited {cases}/8391 cases; {len(violations)} failed local premises", flush=True)
    finally:
        f.step = native
    return dict(cases=cases, finite_run_scanner_entries=calls,
                unsafe_local_entries=len(violations),
                unsafe_cases=len({(v["pc"], v["zero"]) for v in violations}),
                violations=violations, seconds=time.monotonic() - began,
                scope_note="Entries whose scanned symbolic atom is a finite unary run are counted. Infinite outer Blank atoms are omitted; they satisfy the three-zero contraction premise by definition.",
                operation_counts={str(k): v for k, v in Counter((r["op"], r["zero"]) for r in violations).items()})


def main():
    assert __debug__
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--reference", required=True, type=Path)
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    result = run(args.reference.resolve())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "violations"}, indent=2))


if __name__ == "__main__":
    main()
