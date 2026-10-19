#!/usr/bin/env python3
"""Exact finite blank startup, checked with sparse and dense tape encodings."""
from pathlib import Path
import argparse
import hashlib
import json
from verify_runtime import parse_table, require


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--table', type=Path, required=True)
    p.add_argument('--steps', type=int, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    require(a.steps > 0, 'Positive startup length required')
    table = parse_table(a.table)
    q, h, ones = 95, 0, set()
    lo = hi = h
    for tick in range(a.steps):
        require(q != 254, 'Premature halt')
        w, d, z = table[q, int(h in ones)]
        if w:
            ones.add(h)
        else:
            ones.discard(h)
        q, h = z, h+d
        lo, hi = min(lo, h), max(hi, h)
    # The exact frozen K230 seed and frame, independently specified.
    want = {-6, 176}
    vals = [0, 0, 0, 3, 0, 0, 3, 0, 0] + [1]*167
    pos = 177
    for v in vals:
        pos += 1
        want.update(range(pos, pos+v+1))
        pos += v+1
    require(q == 96 and h == -5 and ones == want, 'Wrong complete startup frame')
    # Independent fixed-array representation, with checked access bounds.
    origin = 8192
    tape = bytearray(32768)
    q2, h2 = 95, origin
    for tick in range(a.steps):
        require(0 <= h2 < len(tape), 'Dense bound exhausted')
        w, d, z = table[q2, tape[h2]]
        tape[h2] = w
        h2 += d
        q2 = z
    recovered = {i-origin for i, b in enumerate(tape) if b}
    require((q2, h2-origin, recovered) == (q, h, want), 'Independent replay differs')
    receipt = dict(status='PASS_EXACT_BLANK_STARTUP_AND_DENSE_REPLAY',
                   table_sha256=hashlib.sha256(a.table.read_bytes()).hexdigest(),
                   checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                   steps=a.steps, final_state=q, final_head=h,
                   marker=-6, header=176, gap=181,
                   physical_registers=vals[:9],
                   logical_registers=[3, 0, 0, 0, 3, 0, 0, 0, 0],
                   physical_slot_of_logical=[6, 2, 0, 4, 3, 7, 8, 5, 1],
                   spare_count=167, spare_value=1,
                   one_cells=sorted(ones), all_other_cells_zero=True,
                   accessed_range=[lo, hi],
                   scope='Exact finite initialization; runtime is established separately by induction.')
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps({k: v for k, v in receipt.items() if k != 'one_cells'}, indent=2))


if __name__ == '__main__':
    main()
