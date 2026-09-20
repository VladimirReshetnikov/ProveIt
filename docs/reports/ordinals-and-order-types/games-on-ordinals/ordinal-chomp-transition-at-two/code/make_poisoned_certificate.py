#!/usr/bin/env python3
"""Generate the poisoned-convention bounded-Grundy certificate for S=<4,6,9>.

Python 3.9+, standard library only.  The cutoff value 2 means 'at least 2',
not the exact Grundy value 2.  All finite games here have their zero removed.
This generator and the independent exact verifier share no game solver.

Unlike code/build_certificates.py, which replays documented candidate repeat
indices, this program SEARCHES: it keeps a dictionary of complete boundary
states and discovers the first repetition, then derives the period onset.
Its ideals are ordered by cardinality and then lexicographically, which is a
different column order from the ascending bit masks of certificates/s469.json;
its labels are poisoned, i.e. one less than the unpoisoned labels there.
"""
from functools import lru_cache
from pathlib import Path
import argparse
import json
from typing import Dict, FrozenSet, List, Sequence, Tuple

GENERATORS = (4, 6, 9)
GAPS = (1, 2, 3, 5, 7, 11)
CONDUCTOR, FROBENIUS, CUTOFF = 12, 11, 2


def member(n: int) -> bool:
    return n >= 0 and n not in GAPS


def mex(values: Sequence[int]) -> int:
    used = set(values)
    result = 0
    while result in used:
        result += 1
    return result


@lru_cache(maxsize=None)
def finite_value(position: FrozenSet[int]) -> int:
    """Literal finite-poset recursion; 0 is never included in position."""
    return mex([finite_value(frozenset(z for z in position
                                      if not member(z - move)))
                for move in position])


def ideals() -> List[FrozenSet[int]]:
    result = []
    for mask in range(1 << len(GAPS)):
        current = frozenset(g for i, g in enumerate(GAPS) if mask >> i & 1)
        if all(b in current for a in current for b in GAPS
               if member(a - b)):
            result.append(current)
    return sorted(result, key=lambda c: (len(c), tuple(sorted(c))))


def position(x: int, c: FrozenSet[int]) -> FrozenSet[int]:
    return frozenset(n for n in range(1, x) if member(n)) | frozenset(x + g for g in c)


def generate(max_steps: int = 10000) -> Dict:
    cs = ideals()
    index = {c: i for i, c in enumerate(cs)}
    full = index[frozenset(GAPS)]
    recent = [[index[frozenset(g for g in GAPS if g < d or g - d in c)]
               for d in range(1, FROBENIUS + 1)] for c in cs]
    tails = [[index[frozenset(g for g in c if not member(g - a))]
              for a in sorted(c)] for c in cs]
    rows = {x: tuple(min(CUTOFF, finite_value(position(x, c))) for c in cs)
            for x in range(CONDUCTOR, CONDUCTOR + FROBENIUS)}
    early = []
    prefix = set()
    for y in range(1, CONDUCTOR):
        if member(y):
            ap = frozenset(z for z in range(1, y + FROBENIUS + 1)
                           if member(z) and not member(z - y))
            value = finite_value(ap)
            early.append([y, value])
            if value < CUTOFF:
                prefix.add(value)
    seen = {}
    first = repeat = None
    for x in range(CONDUCTOR + FROBENIUS, max_steps + 1):
        key = (tuple(rows[y] for y in range(x - FROBENIUS, x)), tuple(sorted(prefix)))
        if key in seen:
            first, repeat = seen[key], x
            break
        seen[key] = x
        row = []
        for i, c in enumerate(cs):
            options = set(prefix)
            options.update(rows[x-d][recent[i][d-1]] for d in range(1, FROBENIUS + 1))
            options.update(row[j] for j in tails[i])
            row.append(min(CUTOFF, mex(options)))
        rows[x] = tuple(row)
        old = rows[x - FROBENIUS][full]
        if old < CUTOFF:
            prefix.add(old)
    if first is None or repeat is None:
        raise RuntimeError("No state repetition found within the requested bound")
    period = repeat - first
    nonperiodic = [x for x in rows if x + period in rows and rows[x] != rows[x + period]]
    start = max(nonperiodic) + 1 if nonperiodic else CONDUCTOR
    return {
        "format": "ordinal-chomp-bounded-grundy-certificate-v1",
        "generators": list(GENERATORS), "gaps": list(GAPS),
        "conductor": CONDUCTOR, "frobenius": FROBENIUS,
        "cutoff": CUTOFF,
        "label_meaning": {"0": "exactly 0", "1": "exactly 1", "2": "at least 2"},
        "convention": "normal poset play after deleting the poisoned element 0",
        "ideals": [sorted(c) for c in cs], "full_ideal_index": full,
        "early_apery_values": early,
        "row_first": min(rows), "row_last": max(rows),
        "rows": ["".join(map(str, rows[x])) for x in range(min(rows), max(rows) + 1)],
        "prefix_low_values": sorted(prefix),
        "state_first": first, "state_repeat": repeat,
        "window_length": FROBENIUS, "period": period, "period_start": start,
        "transition_recent_indices": recent, "transition_tail_indices": tails,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    default = Path(__file__).resolve().parents[1] / "certificates" / "s469_poisoned.json"
    parser.add_argument("--output", type=Path, default=default)
    parser.add_argument("--max-steps", type=int, default=10000)
    args = parser.parse_args()
    certificate = generate(args.max_steps)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    # newline="\\n" keeps the bytes, and therefore the published SHA-256,
    # identical on every platform.
    with args.output.open("w", encoding="utf-8", newline="\n") as handle:
        handle.write(json.dumps(certificate, indent=2) + "\n")
    print("Generated", args.output.name)
    print("Gap ideals:", len(certificate["ideals"]))
    print("Rows: {row_first}..{row_last}; states {state_first} and {state_repeat} coincide".format(**certificate))
    print("Eventual period: {period}, beginning at row {period_start}".format(**certificate))
    full = certificate["full_ideal_index"]
    print("Full-ideal labels:", sorted(set(row[full] for row in certificate["rows"])))


if __name__ == "__main__":
    main()
