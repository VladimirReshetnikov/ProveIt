#!/usr/bin/env python3
"""Check the release manifest, nested frozen manifests, and literal table.

This is an integrity check, not a substitute for candidate/reproduce.py.
It uses only Python's standard library and never modifies bundled files.
"""
from pathlib import Path
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_text_manifest(path):
    count = 0
    for line in path.read_text().splitlines():
        if not line:
            continue
        expected, name = line.split('  ', 1)
        target = path.parent / name
        if not target.is_file() or digest(target) != expected:
            raise SystemExit('Manifest mismatch: ' + str(target.relative_to(ROOT)))
        count += 1
    return count


def main():
    if not __debug__ or sys.flags.optimize:
        raise SystemExit('Run without -O.')
    payloads = check_text_manifest(ROOT / 'SHA256SUMS')
    comparison = check_text_manifest(ROOT / 'comparison/SHA256SUMS')
    research = check_text_manifest(ROOT / 'research/SHA256SUMS')
    candidate = json.loads((ROOT / 'candidate/SHA256SUMS.json').read_text())
    for name, expected in candidate.items():
        target = ROOT / 'candidate' / name
        assert target.is_file() and digest(target) == expected, name
    table_path = ROOT / 'candidate/machine/machine.tm'
    rows = {}
    for line in table_path.read_text().splitlines():
        q, b, w, d, n = line.split()
        q, b, w, n = map(int, (q, b, w, n))
        assert (q, b) not in rows
        assert b in (0, 1) and w in (0, 1) and d in ('L', 'R')
        rows[q, b] = (w, d, n)
    assert set(rows) == {(q, b) for q in range(194) for b in (0, 1)}
    assert all(0 <= action[2] <= 194 for action in rows.values())
    assert any(action[2] == 194 for action in rows.values())
    assert digest(table_path) == '9933fe380b5242981255a0b75da6b305fc88df7031e753411a51efaf7dbe0dab'
    reached, todo = {0}, [0]
    while todo:
        q = todo.pop()
        for b in (0, 1):
            n = rows[q, b][2]
            if n < 194 and n not in reached:
                reached.add(n)
                todo.append(n)
    assert reached == set(range(194))
    printed = {}
    for line in (ROOT / 'report/transition_table.tex').read_text().splitlines():
        if not re.match(r'^\d+ & ', line):
            continue
        cells = line.rstrip('\\').split(' & ')
        assert len(cells) == 6
        for offset in (0, 3):
            state = int(cells[offset])
            for bit in (0, 1):
                match = re.fullmatch(r'\$\((\d+),([LR]),(\d+)\)\$', cells[offset + bit + 1])
                assert match, cells
                w, d, n = match.groups()
                printed[state, bit] = (int(w), d, int(n))
    assert printed == rows
    assert (ROOT / 'report/pa194ax11q6.pdf').read_bytes().startswith(b'%PDF-')
    print(json.dumps({
        'status': 'PASS', 'release_payloads': payloads,
        'comparison_payloads': comparison, 'candidate_payloads': len(candidate),
        'research_payloads': research,
        'working_states': 194, 'transitions': len(rows),
        'all_working_states_graph_reachable': True,
        'printed_transition_table': 'EXACT_MATCH',
        'scope': 'Integrity and table identity; run the physical/proof replays separately.'
    }, indent=2))


if __name__ == '__main__':
    main()
