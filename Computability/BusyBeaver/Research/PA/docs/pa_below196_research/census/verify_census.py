#!/usr/bin/env python3
"""Independently check the selected 196-state census, without theorem claims.

Only Python's standard library is used. The supplied U208 checker additionally
replays its eighteen finite local helper certificates; it is attributed code.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def require(p, message):
    if not p:
        raise ValueError(message)


def read(path):
    rows = {}
    for line in path.read_text(encoding='utf-8-sig').splitlines():
        line = line.split('#')[0].strip()
        if not line:
            continue
        q, b, w, d, t = line.split()
        q, b, w, t = map(int, (q, b, w, t))
        require(b in (0, 1) and w in (0, 1) and d in ('L', 'R'), 'bad action')
        require((q, b) not in rows, 'duplicate row')
        rows[q, b] = w, d, t
    return rows


def canonical(rows, start):
    states = {q for q, b in rows}
    require(set(rows) == {(q, b) for q in states for b in (0, 1)}, 'incomplete table')
    mapping = {start: 0}
    order = [start]
    serial = []
    for q in order:
        for b in (0, 1):
            w, d, t = rows[q, b]
            if t not in states:
                nt = -1
            else:
                if t not in mapping:
                    mapping[t] = len(mapping)
                    order.append(t)
                nt = mapping[t]
            serial.append([mapping[q], b, w, d, nt])
    return serial, mapping


def digest(obj):
    return hashlib.sha256(json.dumps(obj, separators=(',', ':')).encode()).hexdigest()


def main():
    manifest = json.loads((ROOT / 'tables196/manifest.json').read_text())
    classes = set()
    records = []
    for e in manifest['tables']:
        p = ROOT / 'tables196' / e['file']
        require(hashlib.sha256(p.read_bytes()).hexdigest() == e['sha256'], 'input bytes differ')
        t = read(p)
        require(set(t) == {(q, b) for q in range(196) for b in (0, 1)}, '196-state row domain differs')
        require({v[2] for v in t.values()} - set(range(196)) == {196}, 'halt domain differs')
        c, names = canonical(t, e['start'])
        require(len(names) == 196, 'not all196 states graph-reachable')
        h = digest(c)
        require(h == e['canonical_sha256'], 'rooted graph differs')
        classes.add(h)
        records.append({'name':e['name'], 'states':196, 'rows':392, 'rooted_canonical_sha256':h})
    require(len(records) == len(classes) == 15, '15-class census failed')
    rejected = json.loads((ROOT / 'rejected195/manifest.json').read_text())
    for e in rejected['files']:
        p = ROOT / 'rejected195' / e['file']
        require(hashlib.sha256(p.read_bytes()).hexdigest() == e['sha256'], 'diagnostic bytes differ')
        t = read(p)
        require(len(t) == 390 and len({q for q,b in t}) == 195, 'diagnostic row count differs')
    with tempfile.TemporaryDirectory() as temp:
        output = Path(temp) / 'u208.json'
        subprocess.run([sys.executable, str(ROOT / 'u208/compare_designs.py'), '--output', str(output)], check=True, capture_output=True, text=True)
        u208 = json.loads(output.read_text())
    result = {'status':'PASS', 'designated196_tables':len(records), 'designated196_rooted_graph_classes':len(classes),
              'two_experimental_MP_tables_included':True, 'original208_tables':u208['original208_presentations'],
              'original208_graph_classes':u208['original208_graph_classes'],
              'additional208_tables':u208['additional208_presentations'],
              'all_designated208_graph_classes':u208['total_accepted208_graph_classes'],
              'rejected195_literal_files':len(rejected['files']),
              'scope':'Finite graph and byte census plus attributed local U208 helper proofs. Does not certify195 candidates or any internal-PA biconditional.',
              'tables196':records}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
