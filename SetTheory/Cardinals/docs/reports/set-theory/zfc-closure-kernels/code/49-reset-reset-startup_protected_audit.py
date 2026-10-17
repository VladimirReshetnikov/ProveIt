#!/usr/bin/env python3
"""Find startup-only mutation scope while retaining every runtime contract.

The exact current permutation252 table has no such rows. This script records
the complete conservative protected footprint before considering mutations;
it does not turn a bounded blank trace into a global transition invariant.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib
import json
from pathlib import Path
import sys

from late_start_credit import certify_control_root


def ordered(items):
    return sorted([list(item) for item in items], key=lambda p: (int(p[0]), p[1]))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--machine-code", type=Path, required=True)
    parser.add_argument("--table", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--bootstrap-bound", type=int, default=100000)
    args = parser.parse_args()
    machine_code = args.machine_code.resolve()
    sys.path.insert(0, str(machine_code))
    backend = importlib.import_module("joint_rotation_search")
    table = backend.read_table(args.table)
    # Replay the unchanged arbitrary-gap/named-register runtime obligations.
    certificate, literal = backend.certify(table, backend.NODES, backend.ROOT_NODE)
    assert certificate["passed"] and certificate["cases"] == 8391
    assert all(table[k] == backend.BASE253[k] for k in backend.BOX_PAIRS)
    boxes = backend.BOX_PAIRS
    protected = literal | boxes
    mutable = set(table) - protected
    working = {q for q, _ in table}
    protected_states = {q for q, _ in protected}
    # Replay the exact finite blank initialization, then apply the new criterion
    # to its observed complete root frame, after the physical-register mapping.
    bootstrap, boot_rows = backend.boot(table, args.bootstrap_bound)
    assert bootstrap["outcome"] == "zero_root" and bootstrap["steps"] == 82552
    physical = bootstrap["frame"]["primary"]
    logical = [physical[backend.PERM[backend.PHYS[r]]] for r in range(9)]
    N, T, W, A, D, H, X, Y, L = logical
    root_certificate = certify_control_root(L, N, A, X, Y)
    assert root_certificate["accepted"]
    # Empty mutation domain is a substantive scoped conclusion. A runtime row
    # may not be altered merely because it was not seen in this blank prefix.
    assert not mutable and not (working - protected_states)
    result = dict(
        table_sha256=sha(args.table),
        runtime_certificate=certificate,
        runtime_literal_rows=len(literal),
        protected_box_rows=len(boxes),
        overlapping_rows=len(literal & boxes),
        all_protected_rows=len(protected),
        working_states=len(working),
        mutable_startup_rows=ordered(mutable),
        removable_startup_states=sorted(working - protected_states, key=int),
        observed_bootstrap_only_rows=ordered(boot_rows - protected),
        runtime_literal_footprint=ordered(literal),
        box_support_footprint=ordered(boxes),
        bootstrap=bootstrap,
        logical_root_vector=logical,
        reset_root_certificate=root_certificate,
        proposed_table_mutations=0,
        mutation_search_outcome="empty eligible domain under retained runtime contracts",
        new_sub252_machine=False,
        scope="Conservative syntactic runtime-proof footprint, not a semantic necessity or global minimality theorem.",
        input_code_sha256={name: sha(machine_code / name) for name in
                          ("joint_rotation_search.py", "strict_affine.py")},
        audit_code_sha256=sha(Path(__file__)),
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: result[k] for k in
          ("runtime_certificate", "runtime_literal_rows", "protected_box_rows",
           "overlapping_rows", "all_protected_rows", "working_states",
           "mutable_startup_rows", "removable_startup_states",
           "proposed_table_mutations", "mutation_search_outcome")}, indent=2))


if __name__ == "__main__":
    main()
