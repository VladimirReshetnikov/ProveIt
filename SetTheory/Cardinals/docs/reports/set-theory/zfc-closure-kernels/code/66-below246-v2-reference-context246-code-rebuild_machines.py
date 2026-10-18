#!/usr/bin/env python3
"""Rebuild Prefix246 directly from the pinned ProveIt permutation252 table.

Derived from the attributed Prefix250 independent-audit rebuild driver.
This adapter changes only the exact machine construction and numbering;
check_macro_inductions.py retains its original symbolic rule semantics.
"""
from __future__ import annotations
import argparse
from hashlib import sha256
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
BASE_SHA256 = '939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713'
PROGRAM_SHA256 = '1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'
OLD_FINAL_SHA256 = '303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee'
CANONICAL_SHA256 = '89cda615b3ea9fcac07ad6b08e0351faa34841a56935b6f5846d3920f13bc0fc'
PHYSICAL = (6, 2, 0, 4, 3, 7, 8, 5, 1)
PATCH = {
    (30, 1): (0, 'R', 95),
    (60, 0): (0, 'R', 20),
    (75, 0): (1, 'R', 255),
    (75, 1): (1, 'L', 63),
    (109, 0): (0, 'R', 75),
    (131, 0): (0, 'L', 48),
    (255, 0): (1, 'L', 255),
    (255, 1): (1, 'L', 131),
}
REMOVED = {0, 1, 3, 43, 59, 85, 97}

def digest(path):
    return sha256(path.read_bytes()).hexdigest()

def read_table(path):
    table, start = {}, None
    for line in path.read_text(encoding='ascii').splitlines():
        if line.startswith('#! start '): start = int(line.split()[-1])
        if not line or line.startswith('#'): continue
        q, b, w, d, t = line.split()
        q, b, w, t = map(int, (q, b, w, t))
        assert b in (0, 1) and w in (0, 1) and d in ('L', 'R')
        assert (q, b) not in table
        table[q, b] = w, d, t
    return table, start

def encode(table, start):
    return f'#! start {start}\n' + ''.join(
        f'{q} {b} {w} {d} {t}\n'
        for (q, b), (w, d, t) in sorted(table.items()))

def build():
    path = ROOT/'sources/baseline252_old.tm'
    assert digest(path) == BASE_SHA256
    baseline, start = read_table(path)
    assert start == 64 and len(baseline) == 504
    assert {q for q, b in baseline} == set(range(254)) - {5, 8}
    table = {key: row for key, row in baseline.items() if key[0] not in REMOVED}
    for key, row in PATCH.items():
        assert baseline.get(key) != row
        table[key] = row
    states = {q for q, b in table}
    assert states == (set(range(254)) - {0, 1, 3, 5, 8, 43, 59, 85, 97}) | {255}
    assert len(states) == 246 and len(table) == 492
    assert set(table) == {(q, b) for q in states for b in (0, 1)}
    assert {t for w, d, t in table.values()} - states == {254}
    assert [(key, row) for key, row in table.items() if row[2] == 254] == [((77, 1), (1, 'R', 254))]
    assert sha256(encode(table, 95).encode('ascii')).hexdigest() == OLD_FINAL_SHA256
    return table

def program_sites():
    path = ROOT/'sources/Prog254.v'
    assert digest(path) == PROGRAM_SHA256
    source = path.read_text(encoding='ascii').split('Definition p254_tab', 1)[1]
    body = source.split('[', 1)[1].split('].', 1)[0]
    edge = r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    pattern = r'\((' + edge + r'),\s*(' + edge + r')\)'
    rows = re.findall(pattern, body)
    assert len(rows) == 6459
    assert not re.sub(r'[\s;]', '', re.sub(pattern, '', body))
    seen, sites = set(), []
    def visit(node, prefix, active):
        assert node not in active and 0 <= node < len(rows)
        seen.add(node)
        for bit, term in enumerate(rows[node]):
            kind, *arg = term.split()
            value = int(arg[0]) if arg else None
            pc = prefix + str(bit)
            if kind == 'CN': visit(value, pc, active | {node})
            else:
                if kind in ('CI', 'CD'): assert value in range(9)
                sites.append((pc, kind, value))
    visit(0, '', set())
    assert seen == set(range(6459)) and len(sites) == 6460
    assert len({pc for pc, kind, value in sites}) == 6460
    return sites

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check', action='store_true')
    args = ap.parse_args()
    if not __debug__: ap.error('Assertions are required; do not use -O.')
    table = build()
    order = [95] + sorted({q for q, b in table} - {95})
    mapping = {old: new for new, old in enumerate(order)} | {254: 246}
    canonical = {(mapping[q], b): (w, d, mapping[t])
                 for (q, b), (w, d, t) in table.items()}
    sites = program_sites()
    canonical_text = encode(canonical, 0)
    assert sha256(canonical_text.encode('ascii')).hexdigest() == CANONICAL_SHA256
    files = {
        'machine/zfc_prefix246_old.tm': encode(table, 95),
        'machine/zfc_prefix246.tm': canonical_text,
        'machine/renumbering.json': json.dumps(dict(start_old=95, halt_old=254, halt_canonical=246,
            canonical_to_old=order, old_to_canonical=mapping), indent=2)+'\n',
        'results/instruction-sites.json': json.dumps(sites, indent=2)+'\n',
    }
    for name, data in files.items():
        path = ROOT/name
        if args.check: assert path.read_text(encoding='ascii') == data, name
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(data, encoding='ascii')
    result = dict(status='PASS', working_states=246, binary_rows=492,
        baseline_sha256=BASE_SHA256, program_sha256=PROGRAM_SHA256,
        source_tree_nodes=6459, instruction_sites=6460,
        guarded_instruction_cases=sum(2 if op == 'CD' else 1 for pc, op, r in sites),
        removed_old_states=sorted(REMOVED), changed_retained_rows=6, added_rows=2,
        start_old=95, halt_old=254, halt_canonical=246,
        final_old_sha256=OLD_FINAL_SHA256, final_canonical_sha256=CANONICAL_SHA256,
        physical_of_logical=PHYSICAL)
    if not args.check:
        (ROOT/'results/rebuild.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__': main()
