#!/usr/bin/env python3
"""Independently replay the rejected runtime193 startup certificates.

No search or source-calculus assumptions are needed for these finite traces.
The default is read-only; --out optionally writes a fresh verification receipt.
"""
from pathlib import Path
import argparse
import hashlib
import json

HERE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("original", type=Path, nargs="?",
                        default=HERE.parent / "reference/haz/inputs/pa194.native.tm")
    parser.add_argument("certificates", type=Path, nargs="?", default=HERE)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit("Run Python without -O.")
    metadata = json.loads((args.certificates / "summary.json").read_text())
    assert hashlib.sha256(args.original.read_bytes()).hexdigest() == metadata["input_sha256"]
    original = {}
    for line in args.original.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        q, bit, w, direction, target = line.split()
        original[int(q), int(bit)] = int(w), -1 if direction == "L" else 1, int(target)
    base = {key: (w, d, 88 if target == 301 else target)
            for key, (w, d, target) in original.items() if key[0] != 301}
    base[88, 0], base[51, 0] = (0, -1, 51), (0, 1, 122)
    states = {q for q, _ in base}
    assert len(states) == 193 and len(base) == 386
    assert {q for _, _, q in base.values()} - states == {254}
    assert original[16, 1] == base[122, 1] == (0, -1, 1)
    reports = []
    for variant in metadata["variants"]:
        table = dict(base)
        _, direction, target = table[198, 0]
        table[198, 0] = variant["append"], direction, target
        records = json.loads((args.certificates / variant["certificate"]).read_text())
        seen, counts, maximum = set(), {}, 0
        for record in records:
            q, head = record["initial_state"], record["initial_head"]
            assert (q, head) not in seen
            seen.add((q, head))
            ones = {0} if variant["kind"] == "onebit" else set()
            snapshots = []
            for row in record["trace"]:
                snapshots.append((q, head, ones.copy()))
                assert row[:3] == [q, head, int(head in ones)]
                w, direction, target = table[q, int(head in ones)]
                assert row[3:] == [w, direction, target]
                (ones.add if w else ones.discard)(head)
                q, head = target, head + direction
            assert len(record["trace"]) == record["steps"]
            status = record["status"]
            if status == "HALT":
                assert q == 254
            elif status == "RAY":
                assert head not in ones
                w, direction, target = table[q, 0]
                assert target == q
                assert (not ones or direction == -1 and head < min(ones)
                        or direction == 1 and head > max(ones))
                assert (q, head, sorted(ones)) == (record["q"], record["head"], record["ones"])
            elif status == "EXACT_LOOP":
                assert (q, head, ones) == snapshots[record["from"]]
            elif status == "BLANK_CYCLE":
                old_q, _, old_ones = snapshots[record["from"]]
                assert old_q == q and not old_ones and not ones
                assert all(row[3] == 0 for row in record["trace"][record["from"]:])
            else:
                raise AssertionError("An open simulation is not a proof: " + status)
            counts[status] = counts.get(status, 0) + 1
            maximum = max(maximum, len(record["trace"]))
        expected = {(q, h) for q in states for h in
                    ((-1, 1) if variant["kind"] == "onebit" else (0,))}
        assert seen == expected and len(records) == len(expected)
        assert counts == variant["counts"] and maximum == variant["max_steps"]
        reports.append(dict(append=variant["append"], kind=variant["kind"],
                            counts=counts, max_steps=maximum))
    result = dict(status="PASS", working_states=193,
        all_blank_and_onebit_entries_classified=True, reports=reports,
        scope="Exact transplanted core, either spare bit, all old blank starts and one-bit entries. Other core edits are not excluded.")
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
