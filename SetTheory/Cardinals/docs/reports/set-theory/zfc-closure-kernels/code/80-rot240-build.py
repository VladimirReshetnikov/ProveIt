#!/usr/bin/env python3
"""Reconstruct every new finite input in memory and compare packaged bytes.

This default check never overwrites a table, source list, or renumbering.
--output writes only an optional JSON reconstruction receipt.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import sys

if not __debug__ or sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE') not in (None, '', '0'):
    raise RuntimeError('Enabled assertions required; disable -O and PYTHONOPTIMIZE')

ROOT = Path(__file__).resolve().parent
PINS = {
    'reference/baseline241_old.tm': '1fa8526c3c971d5a48868599eaed890f614c5a79256e51622d3e32a64229f3a3',
    'reference/baseline_sites.json': '3ee984818f0bdfd2c4daae72aeb14340572e34d73f5cdb5616b6d29d78fcd7f4',
    'reference/rotated241_old.tm': '88a1f42b01b7e2b4bf29bc1b3819b78f1e7a17cefaefbc003654f2f5cc202c2f',
    'machines/zfc240_old.tm': '547dd69da66f66dd48238a53d34b52a3ce85bb6c7d01534dd1cfb815507f248f',
    'machines/zfc240.tm': '508b55a6dfdf96a42f09c49e410e078ae7478a1d0257d78d25503b4da24541cd',
    'machines/sites_logical.json': '74b1e7f73cc3ffe7761e36ab2d57a26e0ba34d3ac624f2472799e6ac41d5a51d',
}
MACRO_ROOTS = (
    '11101001001011000011',
    '1110100100101110011',
    '1110100101100011',
    '111110011',
)
ROTATION_PATCH = {(142, 0): (0, 'R', 72), (142, 1): (1, 'R', 17)}
FOLD_PATCH = {(72, 0): (0, 'L', 144), (72, 1): (1, 'L', 36), (79, 1): (1, 'R', 72)}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def parse_table(data):
    result = {}
    for line in data.decode('ascii').splitlines():
        if not line or line.startswith('#'):
            continue
        q, bit, write, direction, target = line.split()
        q, bit, write, target = map(int, (q, bit, write, target))
        assert (q, bit) not in result
        assert q >= 0 and target >= 0 and bit in (0, 1) and write in (0, 1)
        assert direction in ('L', 'R')
        result[q, bit] = write, direction, target
    states = {q for q, _ in result}
    assert set(result) == {(q, b) for q in states for b in (0, 1)}
    return result


def table_bytes(table):
    return ''.join(f'{q} {b} {w} {d} {t}\n' for (q, b), (w, d, t) in sorted(table.items())).encode('ascii')


def json_bytes(value):
    return (json.dumps(value, indent=2) + '\n').encode('utf-8')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Optional JSON receipt; no generated machine is written')
    args = parser.parse_args()
    inputs = {name: (ROOT / name).read_bytes() for name in PINS}
    for name, expected in PINS.items():
        assert digest(inputs[name]) == expected, ('Pinned input changed', name)
    baseline = parse_table(inputs['reference/baseline241_old.tm'])
    assert len(baseline) == 482 and {q for q, b in baseline} >= {95, 96, 90}
    assert {t for w, d, t in baseline.values()} - {q for q, b in baseline} == {254}

    rotated = baseline.copy()
    rotated.update(ROTATION_PATCH)
    assert table_bytes(rotated) == inputs['reference/rotated241_old.tm']
    assert {key for key, value in rotated.items() if value[2] == 90} == {(79, 1)}
    final = rotated.copy()
    final.update(FOLD_PATCH)
    del final[90, 0]
    del final[90, 1]
    assert set(baseline) - set(final) == {(90, 0), (90, 1)}
    assert {key: value for key, value in final.items() if baseline[key] != value} == {**ROTATION_PATCH, **FOLD_PATCH}
    assert b'#! start 95\n' + table_bytes(final) == inputs['machines/zfc240_old.tm']
    states = {q for q, b in final}
    assert len(states) == 240 and len(final) == 480 and 254 not in states
    assert all(t != 90 for w, d, t in final.values())
    assert {t for w, d, t in final.values()} - states == {254}

    order = [95] + sorted(states - {95})
    renumber = {old: new for new, old in enumerate(order)} | {254: 240}
    assert len(renumber) == 241 and set(renumber.values()) == set(range(241))
    assert renumber[95] == 0 and renumber[96] == 84 and renumber[254] == 240
    canonical = {(renumber[q], b): (w, d, renumber[t]) for (q, b), (w, d, t) in final.items()}
    assert table_bytes(canonical) == inputs['machines/zfc240.tm']
    numbering = {'old_to_new': renumber, 'start': 0, 'dispatcher': 84, 'halt': 240}
    renumbering_bytes = (ROOT / 'machines/renumbering.json').read_bytes()
    assert json_bytes(numbering) == renumbering_bytes

    old_sites = json.loads(inputs['reference/baseline_sites.json'])
    assert len(old_sites) == 6459
    old_leaves = {path: (operation, argument) for path, operation, argument in old_sites}
    assert len(old_leaves) == 6459
    expected_old_local = {}
    for p in MACRO_ROOTS:
        expected_old_local.update({p+'00': ('CD', 6), p+'010': ('CI', 5), p+'011': ('CC', 2), p+'1': ('CI', 5)})
    actual_local = {p: e for p, e in old_leaves.items() if any(p.startswith(root) for root in MACRO_ROOTS)}
    assert actual_local == expected_old_local and len(actual_local) == 16
    new_sites = [row for row in old_sites if row[0] not in expected_old_local]
    for p in MACRO_ROOTS:
        new_sites.extend([[p+'0', 'CI', 5], [p+'10', 'CD', 6], [p+'11', 'CC', 2]])
    new_sites.sort()
    assert len(new_sites) == 6455 and sum(2 if op == 'CD' else 1 for p, op, r in new_sites) == 8386
    assert json_bytes(new_sites) == inputs['machines/sites_logical.json']
    assert max(len(p) for p, op, r in new_sites) == 51
    assert [(p, op, r) for p, op, r in new_sites if op == 'CH'] == [('1110100101101', 'CH', None)]

    for name, original in inputs.items():
        assert (ROOT / name).read_bytes() == original, ('Input changed during reconstruction', name)
    assert (ROOT / 'machines/renumbering.json').read_bytes() == renumbering_bytes
    result = {
        'status': 'BUILD_EXACT_RECONSTRUCTION_PASS',
        'working_states': 240, 'binary_rows': 480,
        'start': 0, 'dispatcher': 84, 'halt': 240,
        'deleted_inherited_states': [90],
        'retained_row_edits': [{'state': q, 'read': b, 'write': w, 'direction': d, 'target': t}
                               for (q, b), (w, d, t) in sorted({**ROTATION_PATCH, **FOLD_PATCH}.items())],
        'source_replacement_roots': list(MACRO_ROOTS),
        'source_leaves': 6455, 'guarded_source_cases': 8386,
        'generated_tables_source_and_bijection_byte_identical': True,
        'generated_artifacts_written': False,
        'input_sha256': {**PINS, 'machines/renumbering.json': digest(renumbering_bytes)},
        'scope': 'Exact construction and serialization. Semantic equivalence is checked by the separate source, local-block, runtime and initialization gates.',
    }
    if args.output:
        output = args.output.resolve()
        protected = {ROOT / name for name in PINS} | {ROOT / 'machines/renumbering.json', Path(__file__).resolve()}
        assert output not in protected, 'Receipt would overwrite a construction input'
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(json_bytes(result))
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
