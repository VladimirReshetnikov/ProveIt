#!/usr/bin/env python3
"""Deterministically reconstruct Detour242 from the pinned Combined243 table.

Default: compare reconstructed bytes to the delivered artifacts, without
changing them. --emit DIRECTORY writes a fresh pair of tables and bijection.
--write-tex also regenerates the report's complete transition-table appendix.
"""
from pathlib import Path
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
BASE_SHA = '4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300'
OLD_SHA = 'c8ef2f44d25fee6813164cc59ec05061799397da8cf7f0ea7baab63d32d76e02'
CAN_SHA = 'ef8c07f372c76a73c021f51801f16f28f1e4ca5ead2d4ce6780c2a245a0db245'


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def read(path):
    data = path.read_bytes()
    require(hashlib.sha256(data).hexdigest() == BASE_SHA, 'Wrong baseline bytes')
    rows = {}
    start = None
    for line in data.decode('ascii').splitlines():
        if line.startswith('#! start '):
            require(start is None, 'Duplicate start')
            start = int(line.split()[-1])
        elif line and not line.startswith('#'):
            q, b, w, d, target = line.split()
            q, b, w, target = map(int, (q, b, w, target))
            require((q, b) not in rows, 'Duplicate row')
            require(b in (0, 1) and w in (0, 1) and d in ('L', 'R'), 'Invalid row')
            rows[q, b] = (w, d, target)
    require(start == 95 and len(rows) == 486, 'Wrong baseline convention')
    return rows


def serialize(rows, start):
    lines = [f'#! start {start}']
    lines.extend(f'{q} {b} {w} {d} {target}'
                 for (q, b), (w, d, target) in sorted(rows.items()))
    return ('\n'.join(lines) + '\n').encode('ascii')


def build():
    old = read(ROOT / 'reference/zfc_combined243_old.tm')
    rows = {(q, b): (w, d, 15 if target == 27 else target)
            for (q, b), (w, d, target) in old.items() if q != 27}
    rows[15, 0] = (0, 'L', 32)
    states = {q for q, b in rows}
    require(len(states) == 242 and len(rows) == 484, 'Wrong state count')
    require(set(rows) == {(q, b) for q in states for b in (0, 1)}, 'Partial table')
    require({target for w, d, target in rows.values()} - states == {254}, 'Wrong halt')
    order = [95] + sorted(states - {95}) + [254]
    ren = {q: n for n, q in enumerate(order)}
    canonical = {(ren[q], b): (w, d, ren[target])
                 for (q, b), (w, d, target) in rows.items()}
    mapping = dict(old_to_canonical=ren, canonical_to_old={v: k for k, v in ren.items()},
                   start_old=95, start_canonical=0, halt_old=254, halt_canonical=242,
                   dispatcher_old=96, dispatcher_canonical=ren[96])
    artifacts = {'zfc_detour242_old.tm': serialize(rows, 95),
                 'zfc_detour242.tm': serialize(canonical, 0),
                 'renumbering.json': (json.dumps(mapping, indent=2) + '\n').encode('ascii')}
    require(hashlib.sha256(artifacts['zfc_detour242_old.tm']).hexdigest() == OLD_SHA,
            'Unexpected inherited serialization')
    require(hashlib.sha256(artifacts['zfc_detour242.tm']).hexdigest() == CAN_SHA,
            'Unexpected canonical serialization')
    return artifacts, canonical


def table_tex(rows):
    lines = [r'{\small', r'\begin{longtable}{@{}rll@{}}',
             r'\toprule State & Read 0: write, move, next & Read 1: write, move, next\\',
             r'\midrule\endfirsthead',
             r'\toprule State & Read 0: write, move, next & Read 1: write, move, next\\',
             r'\midrule\endhead', r'\bottomrule\endfoot']
    for q in range(242):
        a, b = rows[q, 0], rows[q, 1]
        lines.append(f'{q} & \\texttt{{{a[0]} {a[1]} {a[2]}}} & '
                     f'\\texttt{{{b[0]} {b[1]} {b[2]}}}\\\\')
    lines.extend([r'\end{longtable}', '}'])
    return '\n'.join(lines) + '\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--emit', type=Path)
    parser.add_argument('--write-tex', action='store_true')
    args = parser.parse_args()
    artifacts, rows = build()
    for name, data in artifacts.items():
        require((ROOT / 'machine' / name).read_bytes() == data, 'Artifact mismatch: ' + name)
    if args.emit:
        args.emit.mkdir(parents=True, exist_ok=True)
        for name, data in artifacts.items():
            (args.emit / name).write_bytes(data)
    if args.write_tex:
        (ROOT / 'machine/transition_table.tex').write_text(table_tex(rows))
    print(json.dumps(dict(status='PASS_EXACT_RECONSTRUCTION', working_states=242,
                          binary_rows=484, canonical_sha256=CAN_SHA,
                          inherited_sha256=OLD_SHA, removed_state=27,
                          changed_rows=[[15, 0], [18, 0], [47, 0], [65, 0]],
                          exact_renumbering_bytes=True), indent=2))


if __name__ == '__main__':
    main()
