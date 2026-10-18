#!/usr/bin/env python3
"""Replay the canonical table from blank using a sparse-set tape.

The independent checker uses original labels and a dense array. This script
does not import its parser, transition loop, reconstruction, or frame parser.
"""
from pathlib import Path
from collections import Counter
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
STEPS = 741241

def main():
    if not __debug__:
        raise RuntimeError("Assertions are required; do not use -O.")
    path = ROOT / "machine/zfc_prefix247.tm"
    raw = path.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == "58bbbda620daf6d4d62f486db05f54d0dccb8373c080c1b5a0b26533e7a3a669"
    table, start = {}, None
    for line in raw.decode("ascii").splitlines():
        if line.startswith("#! start "):
            start = int(line.split()[-1])
        elif line and not line.startswith("#"):
            q, b, w, direction, target = line.split()
            q, b, w, target = map(int, (q, b, w, target))
            assert q in range(247) and b in (0, 1) and w in (0, 1)
            assert target in range(248) and direction in ("L", "R")
            assert (q, b) not in table
            table[q, b] = w, (1 if direction == "R" else -1), target
    assert start == 0 and len(table) == 494
    state, head, ones = start, 0, set()
    uses = Counter()
    for clock in range(STEPS):
        assert state != 247, ("early halt", clock)
        key = state, int(head in ones)
        uses[key] += 1
        write, movement, target = table[key]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += movement
        state = target
    assert (state, head) == (89, -5)
    marker, header = -6, 245
    primary = [0, 0, 0, 3, 0, 0, 3, 0, 0]
    spares = [1] * 235
    expected = {marker, header}
    cursor = header + 1
    for value in primary + spares:
        expected.update(range(cursor + 1, cursor + value + 2))
        cursor += value + 2
    assert ones == expected and len(ones) == 487 and max(ones) == 974
    assert uses[0, 0] == 1
    result = dict(status="PASS", literal_steps=STEPS, start=0, halt=247,
        state=state, head=head, marker=marker, header=header,
        empty_program_counter=True, head_to_header_distance=250,
        primary_physical=primary,
        primary_logical=[primary[i] for i in [6, 2, 0, 4, 3, 7, 8, 5, 1]],
        spare_count=235, every_spare_value=1, one_count=487,
        all_one_positions=sorted(ones), all_other_cells_zero=True,
        initializer_read_zero_visits=uses[0, 0],
        scope="Exact finite blank-tape bootstrap, using the delivered canonical table.")
    (ROOT / "results/bootstrap-canonical.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k != "all_one_positions"}, indent=2))

if __name__ == "__main__":
    main()
