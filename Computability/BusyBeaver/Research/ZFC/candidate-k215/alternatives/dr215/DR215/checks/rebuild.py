#!/usr/bin/env python3
"""Deterministic DR215 reconstruction from pinned ST215 data; no optimizer."""
from pathlib import Path
import json
import source_language as sl
from common import (canonical_table, check_census, cli, compact, encode_table,
                    parse_table, pinned, require, sha, write_json)

PATCH = {(199, 1): (1, 1, 12), (206, 0): (0, 1, 76)}
OLD = {(199, 1): (1, 1, 166), (206, 0): (0, 1, 186)}
CHANGED = [958, 963, 1136, 1141]


def run(root, work):
    """Reconstruct all four source edits and both native transition edits."""
    root, work = Path(root), Path(work)
    work.mkdir(parents=True, exist_ok=True)
    source = json.loads(pinned(root, 'inputs/st215.sites.json'))
    old_source = [row.copy() for row in source]
    for row in source[887:1170]:
        if row[1] in ('CI', 'CD') and row[2] in (3, 5):
            row[2] = 8 - row[2]
    changed = [i for i, (a, b) in enumerate(zip(old_source, source)) if a != b]
    require(changed == CHANGED, 'Exact four source changes')
    raw_source = compact(source)
    require(raw_source == pinned(root, 'source/dr215.sites.json'), 'Source reconstruction')
    table, start = parse_table(pinned(root, 'inputs/st215.native.tm'))
    require(start == 0, 'Native start')
    require({k: table[k] for k in OLD} == OLD, 'Patch preconditions')
    table.update(PATCH)
    raw_table = encode_table(table, start)
    require(raw_table == pinned(root, 'machine/dr215.native.tm'), 'Native reconstruction')
    check_census(table, start)
    dense, dense_start, mapping = canonical_table(table, start)
    raw_dense = encode_table(dense, dense_start)
    require(raw_dense == (root / 'machine/dr215.tm').read_bytes(), 'Dense reconstruction')
    require(mapping == {int(k): v for k, v in json.loads(
        (root / 'machine/native-to-dense.json').read_text()).items()}, 'Dense map')
    reach, pending = {start}, [start]
    for q in pending:
        for b in (0, 1):
            z = table[q, b][2]
            if z != 254 and z not in reach:
                reach.add(z)
                pending.append(z)
    require(reach == {q for q, b in table}, 'Every counted state graph reachable')
    for name, raw in [('dr215.sites.json', raw_source),
                      ('dr215.native.tm', raw_table), ('dr215.tm', raw_dense)]:
        (work / ('rebuilt-' + name)).write_bytes(raw)
    result = {
        'status': 'DETERMINISTIC_RECONSTRUCTION_PASS',
        'source_sha256': sha(raw_source), 'native_sha256': sha(raw_table),
        'dense_sha256': sha(raw_dense), 'states': 215, 'rows': 430,
        'graph_reachable_working_states': len(reach), 'native_start': start,
        'native_dispatcher': 84, 'native_halt': 254, 'dense_start': dense_start,
        'dense_dispatcher': mapping[84], 'dense_halt': 215,
        'changed_source_ordinals': changed,
        'table_changes': [{'row': list(k), 'before': list(OLD[k]),
                           'after': list(PATCH[k])} for k in sorted(PATCH)],
    }
    write_json(work / 'rebuild.json', result)
    return result


if __name__ == '__main__':
    cli(run)
