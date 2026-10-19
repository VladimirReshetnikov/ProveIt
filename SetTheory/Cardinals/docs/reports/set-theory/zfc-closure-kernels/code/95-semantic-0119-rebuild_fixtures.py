#!/usr/bin/env python3
"""Independently rebuild the frozen finite fixtures from their retained inputs.

This verifies the baseline table identity, ordered source-leaf transfer,
and every byte of the fixture. It does not establish source reachability or
an unbounded binary-machine simulation theorem.
"""
import argparse
import gzip
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PHYSICAL = (6, 2, 0, 4, 3, 7, 8, 5, 1)
TABLE_HASH = 'f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267'
FIXTURE_HASH = '71fd6d7d0460c3f920ba945c04f2e3a1b571ce070e445ae019417ff0d675abc1'


def paint(pc, gap, registers, spares, head):
    assert gap >= len(pc)
    ones = {head - 1, head + gap}
    ones.update(head + i for i, b in enumerate(pc) if b == '1')
    pos = head + gap + 1
    for value in registers + spares:
        assert value >= 0
        ones.update(range(pos + 1, pos + value + 2))
        pos += value + 2
    return ones


def carry(pc):
    bits = list(pc)
    j = len(bits) - 1
    while j >= 0 and bits[j] == '1':
        bits[j] = '0'
        j -= 1
    if j < 0:
        return None
    bits[j] = '1'
    return ''.join(bits)


def drop(pc, bit, count):
    j = len(pc)
    while count and j:
        j -= 1
        count -= pc[j] == bit
    return pc[:j]


def expected(pc, op, arg, values):
    values = values.copy()
    spares = [1] * 167
    gap, head = 181, 0
    if op == 'CH':
        return head, set()
    if op == 'CI':
        values[PHYSICAL[arg]] += 1
        spares.append(1)
        nxt = carry(pc)
    elif op == 'CD':
        if values[PHYSICAL[arg]]:
            values[PHYSICAL[arg]] -= 1
            gap += 1
            nxt = carry(pc)
        else:
            nxt = carry(drop(pc, '0', 1))
    elif op == 'CB':
        nxt = carry(drop(pc, '0', arg))
    else:
        assert op == 'CC'
        nxt = drop(pc, '1', arg)
    if nxt is None:
        head -= 1
        gap += 1
    return head, paint(nxt or '', gap, values, spares, head)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path,
                    help='Optional destination for decompressed cases.txt')
    args = ap.parse_args()
    table_bytes = (ROOT / 'reference/baseline245-old.tm').read_bytes()
    assert hashlib.sha256(table_bytes).hexdigest() == TABLE_HASH
    table = {}
    for line in table_bytes.decode().splitlines():
        if not line or line.startswith('#'):
            continue
        q, bit, write, direction, target = line.split()
        key = int(q), int(bit)
        assert key not in table and direction in ('L', 'R')
        table[key] = int(write), 1 if direction == 'R' else -1, int(target)
    states = {q for q, bit in table}
    assert len(states) == 245 and len(table) == 490
    assert all((q, bit) in table for q in states for bit in (0, 1))
    assert 254 not in states
    assert all(target in states or target == 254 for _, _, target in table.values())

    text = gzip.decompress((ROOT / 'reference/Prog254.v.gz').read_bytes()).decode()
    body = text.split('Definition p254_tab', 1)[1].split('[', 1)[1].split('].', 1)[0]
    token = r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    row = r'\((' + token + r'),\s*(' + token + r')\)'
    source = re.findall(row, body)
    assert len(source) == 6459
    assert not re.sub(r'[;\s]', '', re.sub(row, '', body))
    old_sites = []

    def walk(node, path):
        for bit, edge in enumerate(source[node]):
            op, *arg = edge.split()
            arg = int(arg[0]) if arg else None
            pc = path + str(bit)
            if op == 'CN':
                walk(arg, pc)
            else:
                old_sites.append([pc, op, arg])

    walk(0, '')
    sites = json.loads((ROOT / 'reference/sites_logical.json').read_text())
    assert len(old_sites) == len(sites) == 6460
    assert [x[1:] for x in old_sites] == [x[1:] for x in sites]
    metadata = json.loads(gzip.decompress(
        (ROOT / 'reference/interval-metadata.json.gz').read_bytes()))
    assert len(metadata) == 8385
    lines = [str(len(table))]
    lines += [' '.join(map(str, (q, bit, *table[q, bit])))
              for q, bit in sorted(table)]
    lines.append(str(len(metadata)))
    for record in metadata:
        index = record['program_index']
        assert old_sites[index] == [record['pc'], record['instruction'],
                                    record['logical_register']]
        pc, op, arg = sites[index]
        values = record['physical_values']
        start = sorted(paint(pc, 181, values, [1] * 167, 0))
        head, result = expected(pc, op, arg, values)
        target = sorted(result)
        assert min(start) >= -1 and max(start) < 1984
        assert not target or (-64 <= min(target) and max(target) < 1984)
        lines.append(' '.join(map(str, [int(op == 'CH'), head, len(start),
                                       *start, len(target), *target])))
    raw = ('\n'.join(lines) + '\n').encode()
    assert hashlib.sha256(raw).hexdigest() == FIXTURE_HASH
    assert raw == gzip.decompress((ROOT / 'inputs/cases.txt.gz').read_bytes())
    eligible = []
    for q in sorted(states - {95, 96}):
        incoming = [key for key, (_, _, target) in table.items()
                    if key[0] != q and target == q]
        if len(incoming) == 1:
            eligible.append(q)
    assert len(eligible) == 137
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_bytes(raw)
    print(json.dumps(dict(
        status='PASS_EXACT_FINITE_FIXTURE_REBUILD', states=245, rows=490,
        cases=8385, source_leaves=6460, eligible_single_entry_states=137,
        pair_merge_recipes=4 * 245 * 244 // 2,
        elimination_recipes=137 * 4 * 244,
        table_sha256=TABLE_HASH, decompressed_fixture_sha256=FIXTURE_HASH,
        gap=181, spare_count=167, spare_values=1,
        source_reachability_claim=False, unbounded_simulation_claim=False
    ), indent=2))


if __name__ == '__main__':
    main()
