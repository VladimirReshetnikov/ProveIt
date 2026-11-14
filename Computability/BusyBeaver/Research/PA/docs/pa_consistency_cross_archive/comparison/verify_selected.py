#!/usr/bin/env python3
"""Independent exact graph census. No halting or consistency theorem is inferred."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def parse(path):
    rows = {}
    for line in path.read_text().splitlines():
        line = line.split('#')[0].strip()
        if not line:
            continue
        q, b, w, d, t = line.split()
        q, b, w, t = map(int, (q, b, w, t))
        if b not in (0, 1) or w not in (0, 1) or d not in ('L', 'R') or (q, b) in rows:
            raise ValueError('Malformed binary transition')
        rows[q, b] = (w, d, t)
    if set(rows) != {(q, b) for q in range(196) for b in (0, 1)}:
        raise ValueError('Not the stated 196-working-state domain')
    if {t for w, d, t in rows.values()} - set(range(196)) != {196}:
        raise ValueError('Halt labels differ')
    return rows

def canonical(rows, start):
    mapping, queue, serial = {start: 0}, [start], []
    for q in queue:
        for b in (0, 1):
            w, d, t = rows[q, b]
            if t == 196:
                nt = -1
            else:
                if t not in mapping:
                    mapping[t] = len(mapping)
                    queue.append(t)
                nt = mapping[t]
            serial.append([mapping[q], b, w, d, nt])
    if len(mapping) != 196:
        raise ValueError('Graph reachability differs')
    return hashlib.sha256(json.dumps(serial, separators=(',', ':')).encode()).hexdigest()

def bisimulation_count(rows):
    part = {q: 0 for q in range(196)}
    while True:
        signatures, refined = {}, {}
        for q in range(196):
            key = tuple((rows[q, b][0], rows[q, b][1], part.get(rows[q, b][2], -1)) for b in (0, 1))
            if key not in signatures:
                signatures[key] = len(signatures)
            refined[q] = signatures[key]
        if part == refined:
            return len(signatures)
        part = refined

def main():
    manifest = json.loads((ROOT / 'selected196.json').read_text())
    records, hashes = [], set()
    for e in manifest['tables']:
        path = ROOT / e['file']
        if hashlib.sha256(path.read_bytes()).hexdigest() != e['bytes_sha256']:
            raise ValueError('Changed table bytes: ' + e['name'])
        rows = parse(path)
        h = canonical(rows, e['start'])
        if h != e['canonical_sha256']:
            raise ValueError('Changed graph: ' + e['name'])
        hashes.add(h)
        records.append({'name': e['name'], 'states': 196, 'rows': 392, 'bisimulation_classes': bisimulation_count(rows)})
    if len(records) != 20 or len(hashes) != 20:
        raise ValueError('Expected twenty distinct selected graphs')
    print(json.dumps({'status': 'PASS', 'selected_tables': 20, 'rooted_graph_classes': len(hashes),
                      'scope': 'Graph/byte facts only; two experimental MP tables are included; no new consistency or nonhalting proof.',
                      'records': records}, indent=2))

if __name__ == '__main__':
    main()
