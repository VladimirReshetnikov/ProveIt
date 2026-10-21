#!/usr/bin/env python3
"""Independent finite replay of every boundary in the calibrated K215 prefix.

The infinite all-tape claim is proved in Lean/Rocq, not inferred from this test.
"""
import argparse
import hashlib
import json
from pathlib import Path

def read(path):
    raw = Path(path).read_bytes()
    rows = {}
    for line in raw.decode().splitlines():
        if not line or line.startswith('#'):
            continue
        q,b,w,d,n = line.split()
        key = int(q), int(b)
        assert key not in rows
        rows[key] = int(w), 1 if d == 'R' else -1, int(n)
    return rows, hashlib.sha256(raw).hexdigest()

def one(rows, q, h, tape):
    w,d,n = rows[q, int(h in tape)]
    if w:
        tape.add(h)
    else:
        tape.discard(h)
    return n, h+d

def replay(oldpath, newpath, output):
    old, oldhash = read(oldpath)
    new, newhash = read(newpath)
    qt = ht = qs = hs = steps = special = 0
    ts, tt = set(), set()
    exceptional = {'124/0': 0, '127/0': 0}
    for index in range(95714):
        if qs == 124:
            assert hs-1 in ts
        if qs == 127:
            assert hs-1 not in ts
        special_now = qs in (124,127) and hs not in ts
        if special_now:
            special += 1
            exceptional[f'{qs}/0'] += 1
        duration = 3 if special_now else 1
        qs,hs = one(old,qs,hs,ts)
        for _ in range(duration):
            qt,ht = one(new,qt,ht,tt)
        steps += duration
        assert qt == (124 if qs == 127 else qs)
        assert ht == hs and ts == tt
    assert (qs, hs, len(ts)) == (84, -8, 95)
    assert special == 63 and steps == 95840
    out = {
        'status': 'passed',
        'old_sha256': oldhash, 'new_sha256': newhash,
        'old_transitions': 95714, 'new_transitions': steps,
        'synchronization_boundaries_checked': 95714,
        'exceptional_old_steps': special, 'exceptional_breakdown': exceptional,
        'terminal_native_control': qs, 'terminal_head': hs,
        'terminal_one_cells': sorted(ts),
        'scope': 'Finite blank-prefix validation; unbounded proof is separate.'
    }
    if output:
        Path(output).write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k != 'terminal_one_cells'},indent=2))

if __name__ == '__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('baseline')
    ap.add_argument('candidate')
    ap.add_argument('--output')
    a=ap.parse_args()
    replay(a.baseline,a.candidate,a.output)
