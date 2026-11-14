#!/usr/bin/env python3
"""Independently check a finite-window invariant using only Python's stdlib.

The construction code is not imported. Both values for every newly exposed
boundary cell are checked. Acceptance is independent of Python assertions.
"""
import gzip, hashlib, json, time
from pathlib import Path

def need(condition, message):
    if not condition:
        raise ValueError(message)

def read_table(path):
    table = {}
    for line in Path(path).read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        words = line.split()
        need(len(words) == 5, 'Malformed row')
        q, b, w, move, z = words
        q, b, w, z = map(int, (q, b, w, z))
        need(b in (0, 1) and w in (0, 1) and move in ('L', 'R'), 'Bad transition')
        need((q, b) not in table, 'Duplicate row')
        table[q, b] = w, 1 if move == 'R' else -1, z
    states = {q for q, b in table}
    need(set(table) == {(q, b) for q in states for b in (0, 1)}, 'Partial table')
    need(all(z in states or z == 254 for w, d, z in table.values()), 'Unknown target')
    return table

def check(root):
    started = time.monotonic()
    table_path = root / 'data/u208.native.tm'
    table = read_table(table_path)
    lines = (root / 'evidence/window7.meta').read_text().splitlines()
    radius, width_count, state_count = map(int, lines[0].split())
    labels, counts = zip(*(tuple(map(int, line.split())) for line in lines[1:]))
    need(width_count == 1 << (2 * radius + 1), 'Window size')
    need(state_count == len(labels) == len(set(labels)), 'State labels')
    need(set(labels) == {q for q, b in table}, 'State domain')
    data = gzip.decompress((root / 'evidence/window7.bin.gz').read_bytes())
    need(len(data) == width_count * state_count, 'Certificate size')
    need(set(data) <= {0, 1}, 'Certificate alphabet')
    windows = {q: data[i * width_count:(i + 1) * width_count]
               for i, q in enumerate(labels)}
    need(windows[0] == bytes([1]) * width_count, 'Not all initial tapes covered')
    need(all(sum(windows[q]) == count for q, count in zip(labels, counts)), 'Bad census')
    checks = 0
    for q in labels:
        for pattern, present in enumerate(windows[q]):
            if not present:
                continue
            read = (pattern >> radius) & 1
            write, direction, target = table[q, read]
            if target == 254:
                continue
            changed = (pattern & ~(1 << radius)) | (write << radius)
            if direction == 1:
                destination = changed >> 1
                boundary = 1 << (2 * radius)
            else:
                destination = (changed << 1) & (width_count - 1)
                boundary = 1
            need(windows[target][destination] == 1, 'Zero-boundary successor missing')
            need(windows[target][destination | boundary] == 1, 'One-boundary successor missing')
            checks += 2
    contexts = json.loads((root / 'evidence/window7.contexts.json').read_text())
    need(set(map(int, contexts)) == set(labels), 'Context state domain')
    cube_count = 0
    for q in labels:
        reconstructed = bytearray(width_count)
        for cube in contexts[str(q)]:
            cube_count += 1
            fixed = {int(x): value for x, value in cube.items()}
            need(all(-radius <= x <= radius and value in (0, 1)
                     for x, value in fixed.items()), 'Bad cylinder')
            start = sum(value << (x + radius) for x, value in fixed.items())
            assignments = [start]
            for x in range(-radius, radius + 1):
                if x not in fixed:
                    bit = 1 << (x + radius)
                    assignments += [value | bit for value in assignments]
            for pattern in assignments:
                reconstructed[pattern] = 1
        need(bytes(reconstructed) == windows[q], 'DNF does not represent invariant')
    return {
        'status': 'PASS', 'radius': radius, 'window_width': 2 * radius + 1,
        'working_states': state_count, 'reachable_abstract_windows': sum(data),
        'universal_successor_checks': checks, 'dnf_cubes': cube_count,
        'initial_state0_all_tapes': True, 'dnf_equal': True,
        'native_sha256': hashlib.sha256(table_path.read_bytes()).hexdigest(),
        'window_sha256': hashlib.sha256(data).hexdigest(),
        'seconds': time.monotonic() - started,
    }
