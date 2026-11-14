#!/usr/bin/env python3
"""Greatest one-step action-preserving control congruence on each frontier table.

All simultaneous control merges are allowed, but both writes and movements
must agree and successors must be congruent. Head shifts, history invariants,
and multistep simulations are outside this quotient family.
"""
from pathlib import Path
import argparse
import hashlib
import json

HERE = Path(__file__).resolve().parent


def parse(path):
    rows = {}
    for line in path.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        q, bit, w, direction, target = line.split()
        rows[int(q), int(bit)] = int(w), direction, int(target)
    states = {q for q, _ in rows}
    halts = {q for _, _, q in rows.values()} - states
    assert len(halts) == 1
    return rows, sorted(states), next(iter(halts))


def refine(rows, states, halt):
    partition = {q: 0 for q in states}
    partition[halt] = -1
    counts = [1]
    while True:
        signatures, new = {}, {halt: -1}
        for q in states:
            signature = tuple((w, d, partition[target]) for w, d, target in (rows[q, 0], rows[q, 1]))
            new[q] = signatures.setdefault(signature, len(signatures))
        counts.append(len(signatures))
        partition = new
        if counts[-1] == counts[-2]:
            break
    classes = {}
    for q in states:
        classes.setdefault(partition[q], []).append(q)
    return counts, list(classes.values())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path, nargs="?", default=HERE / "frontier42")
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit("Run Python without -O.")
    records = []
    for path in sorted(args.directory.glob("*.tm")):
        rows, states, halt = parse(path)
        counts, classes = refine(rows, states, halt)
        records.append(dict(file=path.name, sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
            states=len(states), quotient_states=len(classes), refinement_class_counts=counts,
            nontrivial_classes=[group for group in classes if len(group) > 1]))
    result = dict(scope=__doc__, tables=records,
                  any_reduction=any(r["quotient_states"] < r["states"] for r in records))
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(dict(tables=len(records), any_reduction=result["any_reduction"],
        max_refinement_rounds=max(len(r["refinement_class_counts"]) - 1 for r in records)), indent=2))


if __name__ == "__main__":
    main()
