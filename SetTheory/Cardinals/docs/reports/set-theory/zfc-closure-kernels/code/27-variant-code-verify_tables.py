#!/usr/bin/env python3
"""Independent literal-table audit and complete 253-state finite bootstrap.

This checker establishes finite structural/run facts only. It does not infer
nonhalting or consistency from a finite simulation. Its sparse tape represents
all positions outside the finite set of ones by zero.
"""
from pathlib import Path
import argparse
import hashlib
import json

BASE = Path(__file__).resolve().parents[1]
PINS = {
    'upstream_254.tm': 'd655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb',
    'upstream_253.tm': '84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95',
    'faster_253.tm': 'd5b7a357dbf4dd9d18c8e1aa04dc0c3c0e1b8f349853b7558d1a096a15684412',
}

def load(path):
    raw = path.read_bytes()
    table, start = {}, None
    for line in raw.decode('ascii').splitlines():
        line = line.strip()
        if not line:
            continue
        if line.startswith('#! start '):
            if start is not None:
                raise ValueError('duplicate start header')
            start = int(line.split()[2])
            continue
        if line.startswith('#'):
            continue
        fields = line.split()
        if len(fields) != 5:
            raise ValueError('wrong transition arity')
        q, read, write, direction, target = fields
        q, read, write, target = map(int, (q, read, write, target))
        if read not in (0, 1) or write not in (0, 1) or direction not in ('L', 'R'):
            raise ValueError('not a binary L/R table')
        if (q, read) in table:
            raise ValueError('duplicate transition')
        table[q, read] = (write, -1 if direction == 'L' else 1, target)
    states = {q for q, b in table}
    n = len(states)
    if states != set(range(n)) or start != 0:
        raise ValueError('unexpected working-state convention')
    if set(table) != {(q, b) for q in states for b in (0, 1)}:
        raise ValueError('incomplete table')
    if any(target not in states | {n} for w, d, target in table.values()):
        raise ValueError('unexpected terminal state')
    return raw, table, n

def quotient(table, n):
    classes = [0] * n
    rounds = []
    while True:
        ids = {}
        refined = []
        for q in range(n):
            signature = tuple((w, d, -1 if t == n else classes[t])
                              for w, d, t in (table[q, 0], table[q, 1]))
            refined.append(ids.setdefault(signature, len(ids)))
        rounds.append(len(ids))
        if refined == classes:
            break
        classes = refined
    return rounds

def reachable(table, n):
    seen, todo = {0}, [0]
    while todo:
        q = todo.pop()
        for b in (0, 1):
            t = table[q, b][2]
            if t < n and t not in seen:
                seen.add(t); todo.append(t)
    return len(seen)

def bootstrap_253(table, steps=312975):
    state = head = 0
    ones = set()
    for step in range(steps):
        if state == 253:
            raise ValueError('unexpected halt in boot prefix')
        w, d, state = table[state, int(head in ones)]
        if w:
            ones.add(head)
        else:
            ones.discard(head)
        head += d
    if (state, head) != (33, -17):
        raise ValueError('wrong finite boot endpoint')
    # Boot253.v: left [true], right 40 zeros, header1, then sepsR.
    # sepsR(vs) consists of blocks 0 followed by (v+1) ones.
    physical = [0, 2, 0, 0, 0, 0, 5, 0, 0]
    tail = [0, 0, 1, 0, 0, 0, 0, 0, 1] + [0] * 149
    expected = {head - 1, head + 40}
    position = head + 41
    for value in physical + tail:
        expected.update(range(position + 1, position + value + 2))
        position += value + 2
    if ones != expected:
        raise ValueError('full all-integer tape frame mismatch')
    encoded = json.dumps(sorted(ones), separators=(',', ':')).encode('ascii')
    return {'steps': steps, 'state': state, 'head': head,
            'header_distance': 40, 'logical_registers': [5, 0, 0, 0, 2, 0, 0, 0, 0],
            'physical_registers': physical, 'spare_blocks': len(tail),
            'spare_nonzero_indices': [i for i, v in enumerate(tail) if v],
            'ones': len(ones), 'all_integer_tape_frame_matches': True,
            'sorted_ones_sha256': hashlib.sha256(encoded).hexdigest()}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = {'scope': 'finite table and bootstrap verification; no consistency claim',
              'tables': []}
    for filename, digest in PINS.items():
        raw, table, n = load(BASE / 'machines' / filename)
        actual = hashlib.sha256(raw).hexdigest()
        if actual != digest:
            raise ValueError('source pin differs: ' + filename)
        item = {'filename': filename, 'sha256': actual, 'working_states': n,
                'terminal_state': n, 'transitions': len(table),
                'halt_edges': sum(t == n for w, d, t in table.values()),
                'graph_reachable_working_states': reachable(table, n),
                'exact_quotient_class_counts': quotient(table, n)}
        if n == 253:
            item['bootstrap'] = bootstrap_253(table, 312935 if filename == 'faster_253.tm' else 312975)
        result['tables'].append(item)
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')

if __name__ == '__main__':
    main()
