#!/usr/bin/env python3
"""Independently compare designated U208 tables, preserving every action label.

Usage: python canonical_compare.py ARCHIVE_DIRECTORY OUTPUT_DIRECTORY
Only Python's standard library is required. Input ZIPs are not modified.
"""
from collections import deque
from hashlib import sha256
import json
from pathlib import Path
import sys
from zipfile import ZipFile

SOURCES = [
    ('U208_ConPA_2026-10-29.zip', 'U208_ConPA_2026-10-29/machine/u208.tm'),
    ('U208_ConPA_Conditional_Context_2026-10-29.zip', 'u208_conpa_2026-10-29/machine/u208.tm'),
    ('U208_ConPA_Conditional_Context_2026-10-29.zip', 'u208_conpa_2026-10-29/alternative/u208.tm'),
    ('U208_ConPA_Entry_Context_2026-10-29.zip', 'u208_conpa_entry_context_2026-10-29/machine/u208.tm'),
    ('U208_ConPA_Entry_Context_2026-10-29.zip', 'u208_conpa_entry_context_2026-10-29/machine/u208_compatibility.tm'),
    ('U208_ConPA_History_2026-10-29.zip', 'U208_ConPA_History_2026-10-29/machine/u208.tm'),
    ('U208_ConPA_History_2026-10-29.zip', 'U208_ConPA_History_2026-10-29/machine/compatibility_variant/u208.tm'),
    ('u208_research_2026-10-29.zip', 'u208_research_2026-10-29/machine/u208.tm'),
    ('u208_research_2026-10-29.zip', 'u208_research_2026-10-29/machine/variant_plain/u208.tm'),
]

def require(condition, message):
    if not condition:
        raise ValueError(message)

def canonicalize(data):
    table = {}
    start = 0
    for line in data.decode().splitlines():
        if line.startswith('#! start '):
            start = int(line.split()[-1])
        elif line.strip() and not line.startswith('#'):
            fields = line.split()
            require(len(fields) == 5, 'bad row')
            q, b, w, d, t = fields
            q, b, w, t = map(int, (q, b, w, t))
            require((q, b) not in table and b in (0, 1) and w in (0, 1) and d in ('L', 'R'), 'invalid or repeated row')
            table[q, b] = (w, d, t)
    states = {q for q, _ in table}
    require(set(table) == {(q, b) for q in states for b in (0, 1)}, 'incomplete machine')
    terminals = {t for _, _, t in table.values()} - states
    require(len(terminals) == 1, 'need one distinguished halt target')
    halt = terminals.pop()
    queue = deque([start])
    labels = {start: 0}
    encoding = []
    while queue:
        q = queue.popleft()
        rows = []
        for b in (0, 1):
            w, d, t = table[q, b]
            if t == halt:
                target = 'H'
            else:
                if t not in labels:
                    labels[t] = len(labels)
                    queue.append(t)
                target = labels[t]
            rows.append([w, d, target])
        encoding.append(rows)
    require(set(labels) == states, 'graph-unreachable working states')
    return {'working_states': len(states), 'rows': len(table), 'start': start,
            'halt': halt, 'state_to_canonical': labels, 'canonical_encoding': encoding}

def main():
    archives, destination = map(Path, sys.argv[1:])
    destination.mkdir(parents=True, exist_ok=True)
    inputs = destination / 'inputs'
    inputs.mkdir(exist_ok=True)
    classes = []
    entries = []
    for i, (archive, member) in enumerate(SOURCES):
        archive_bytes = (archives / archive).read_bytes()
        with ZipFile(archives / archive) as z:
            data = z.read(member)
        record = canonicalize(data)
        code = record.pop('canonical_encoding')
        if code not in classes:
            classes.append(code)
        record['class'] = chr(65 + classes.index(code))
        record['canonical_sha256'] = sha256(json.dumps(code, separators=(',', ':')).encode()).hexdigest()
        record['archive'] = archive
        record['archive_sha256'] = sha256(archive_bytes).hexdigest()
        record['member'] = member
        record['input_file'] = f'inputs/u208_{i}.tm'
        record['input_sha256'] = sha256(data).hexdigest()
        (destination / record['input_file']).write_bytes(data)
        entries.append(record)
    require(len(classes) == 2, 'unexpected class count')
    require(all(x['working_states'] == 208 and x['rows'] == 416 for x in entries), 'unexpected state/row count')
    # Independently verify every alleged isomorphism row by row by composing maps.
    for c in ('A', 'B'):
        selected = [e for e in entries if e['class'] == c]
        for entry in selected:
            reconstructed = canonicalize((destination / entry['input_file']).read_bytes())
            require(reconstructed['canonical_encoding'] == classes[ord(c)-65], 'full encoding mismatch')
    result = {'classification': 'rooted, read/write/direction-preserving state renaming',
              'classes': {chr(65+i): code for i, code in enumerate(classes)}, 'entries': entries,
              'class_sizes': {c: sum(e['class'] == c for e in entries) for c in ('A', 'B')},
              'all_encodings_compared': True,
              'limitations': ['Graph reachability is not blank-run reachability.',
                              'This comparison proves neither nonhalting nor arithmetic consistency equivalence.']}
    (destination / 'comparison.json').write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps({k: result[k] for k in ('class_sizes', 'all_encodings_compared')}))

if __name__ == '__main__':
    main()
