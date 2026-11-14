#!/usr/bin/env python3
"""Independently replay all reported synthetic local-fold controls."""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent

def main():
    table = {}
    for line in (HERE / 'control.tm').read_text().splitlines():
        q, bit, write, direction, target = line.split()
        table[int(q), int(bit)] = (int(write), 1 if direction == 'R' else -1, int(target))
    n = len(table) // 2
    counts = {}
    for line in (HERE / 'control_results.txt').read_text().splitlines():
        kind, *fields = line.split()
        values = list(map(int, fields))
        drop, keep = values[:2]
        patches = {}
        if kind in ('ONE', 'SURVIVOR'):
            rest = values[2:]
            for i in range(0, len(rest), 5):
                state, bit, write, direction, target = rest[i:i+5]
                patches[state, bit] = (write, direction, target)
        elif kind == 'THREE':
            rest = values[2:]
            for i in range(0, len(rest), 4):
                key, write, direction, target = rest[i:i+4]
                patches[key//2, key%2] = (write, direction, target)
        elif kind != 'PLAIN':
            raise ValueError(kind)
        def project(q):
            return keep if q == drop else q
        # Check ALL original controls and all 32 windows, including helpers.
        for original in range(n):
            for mask in range(32):
                initial = {i: (mask >> (i+2)) & 1 for i in range(-2, 3)}
                old = table[original, initial[0]]
                goal = dict(initial)
                goal[0] = old[0]
                tape, head, q = dict(initial), 0, project(original)
                matched = False
                for _ in range(16):
                    if q == n or head not in tape:
                        break
                    key = (q, tape[head])
                    write, direction, target = patches.get(key, table[key])
                    tape[head] = write
                    head += direction
                    q = project(target)
                    if (q, head, tape) == (project(old[2]), old[1], goal):
                        matched = True
                        break
                if not matched:
                    raise ValueError(('Invalid reported fold', line, original, mask))
        counts[kind] = counts.get(kind, 0) + 1
    if counts != {'SURVIVOR': 5, 'THREE': 11, 'ONE': 1}:
        raise ValueError(('Unexpected control census', counts))
    print(json.dumps({'status': 'INDEPENDENT_CONTROL_REPLAY_PASS',
                      'outputs': sum(counts.values()), 'kinds': counts,
                      'full_context_obligations': sum(counts.values())*n*32}, indent=2))

if __name__ == '__main__':
    main()
