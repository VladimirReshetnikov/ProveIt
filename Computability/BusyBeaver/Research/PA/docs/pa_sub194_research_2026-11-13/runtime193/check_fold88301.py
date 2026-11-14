#!/usr/bin/env python3
"""Reconstruct the rejected runtime193 core and certify elementary startups.

The result is a startup classification, not a Con(PA) construction. Fuel
exhaustion is explicitly OPEN and is never classified as divergence.
"""
from pathlib import Path
import argparse
import hashlib
import json

HERE = Path(__file__).resolve().parent
PRIMARY = HERE.parent / "reference/haz/inputs/pa194.native.tm"
PRIMARY_SHA = "e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54"


def parse(path):
    table = {}
    for line in path.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        q, b, w, direction, target = line.split()
        table[int(q), int(b)] = int(w), 1 if direction == "R" else -1, int(target)
    return table


def reduce(table):
    assert table[88, 0] == (0, 1, 122)
    assert table[301, 0] == (0, 1, 45)
    assert table[51, 0] == (0, 1, 16)
    table = {key: (w, d, 88 if target == 301 else target)
             for key, (w, d, target) in table.items() if key[0] != 301}
    table[88, 0] = 0, -1, 51
    table[51, 0] = 0, 1, 122
    assert len(table) == 386
    return table


def classify(table, state, head=0, initial_ones=(), fuel=100000):
    ones, seen, blank_seen, trace = set(initial_ones), {}, {}, []
    for step in range(fuel):
        if (state, 0) not in table:
            return dict(status="HALT", steps=step, q=state, head=head,
                        ones=sorted(ones), trace=trace)
        if head not in ones:
            w, direction, target = table[state, 0]
            exterior = (not ones or direction == 1 and head > max(ones)
                        or direction == -1 and head < min(ones))
            if target == state and exterior:
                return dict(status="RAY", steps=step, q=state, head=head,
                            ones=sorted(ones), trace=trace,
                            direction=direction, write=w)
        key = state, head, tuple(sorted(ones))
        if key in seen:
            return {"status": "EXACT_LOOP", "steps": step,
                    "from": seen[key], "trace": trace}
        seen[key] = step
        if not ones:
            if state in blank_seen:
                previous, old_head = blank_seen[state]
                assert all(row[3] == 0 for row in trace[previous:])
                return {"status": "BLANK_CYCLE", "steps": step,
                        "from": previous, "head_delta": head - old_head,
                        "trace": trace}
            blank_seen[state] = step, head
        else:
            blank_seen.clear()
        bit = int(head in ones)
        w, direction, target = table[state, bit]
        trace.append([state, head, bit, w, direction, target])
        (ones.add if w else ones.discard)(head)
        state, head = target, head + direction
    return dict(status="OPEN", steps=fuel, q=state, head=head, ones=sorted(ones))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("table", type=Path, nargs="?", default=PRIMARY)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit("Run Python without -O.")
    digest = hashlib.sha256(args.table.read_bytes()).hexdigest()
    assert digest == PRIMARY_SHA
    table = reduce(parse(args.table))
    args.out.mkdir(parents=True, exist_ok=True)
    output = dict(input_path=str(args.table), input_sha256=digest,
                  working_states=193, variants=[])
    for append in (0, 1):
        _, direction, target = table[198, 0]
        table[198, 0] = append, direction, target
        for kind, heads, ones in (("blank", (0,), ()), ("onebit", (-1, 1), (0,))):
            records, counts = [], {}
            for state in sorted({q for q, _ in table}):
                for head in heads:
                    result = classify(table, state, head, ones)
                    result.update(initial_state=state, initial_head=head)
                    records.append(result)
                    counts[result["status"]] = counts.get(result["status"], 0) + 1
            name = f"append{append}_{kind}.json"
            (args.out / name).write_text(json.dumps(records, indent=2) + "\n")
            output["variants"].append(dict(append=append, kind=kind, counts=counts,
                max_steps=max(r["steps"] for r in records), certificate=name))
    (args.out / "summary.json").write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
