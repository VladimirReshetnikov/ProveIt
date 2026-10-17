#!/usr/bin/env python3
"""Regenerate the shortcut table and finite certificates from the pinned source.

This generator is not trusted by the certificate argument: check_certificate.py
separately checks initial membership and closure of its emitted invariant.
"""
import hashlib
import json
from collections import deque
from pathlib import Path
from check_certificate import parse, expected_boot_shape, canonical_digest, SOURCE_SHA

HERE = Path(__file__).resolve().parent


def main():
    source = (HERE / 'source_zfc253.tm').read_bytes()
    if hashlib.sha256(source).hexdigest() != SOURCE_SHA:
        raise ValueError('source SHA256 differs from the pinned public253 table')
    rows = parse(source)
    masks = [0] * 254
    reached, queue = {(0, 0)}, deque([(0, 0)])
    while queue:
        q, pattern = queue.popleft()
        masks[q] |= 1 << pattern
        if q == 253:
            continue
        write, move, target = rows[q, (pattern >> 2) & 1]
        written = (pattern & ~4) | (write << 2)
        if move == 1:
            shifted, unknown = written >> 1, 16
        else:
            shifted, unknown = (written << 1) & 31, 1
        for next_pattern in (shifted, shifted | unknown):
            pair = (target, next_pattern)
            if pair not in reached:
                reached.add(pair)
                queue.append(pair)
    certificate = {
        'schema': 'binary-tm-window-invariant-v1',
        'source_url': 'https://github.com/mira-emmy/busy-beaver/blob/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253/machine/zfc_253.tm',
        'source_commit': '0d544f2a2e3c18f12278441a74b7879f31cbe856',
        'source_sha256': SOURCE_SHA,
        'radius': 2,
        'encoding': 'bit i of pattern is tape cell head+i-2; bit pattern of state mask means admitted window',
        'abstract_configurations': len(reached),
        'state_pattern_masks': masks,
    }
    (HERE / 'invariant_radius2.json').write_text(json.dumps(certificate, indent=2) + '\n')
    changed = dict(rows)
    changed[60, 0] = (0, 1, 51)
    table = '#! start 0\n'
    for (q, b), (write, move, target) in sorted(changed.items()):
        table += f'{q} {b} {write} {"R" if move == 1 else "L"} {target}\n'
    (HERE / 'zfc253_shortcut.tm').write_text(table)
    endpoint = expected_boot_shape()
    record = {'source_boot_steps': 312975, 'shortcut_boot_steps': 312895,
              'configuration': endpoint, 'configuration_sha256': canonical_digest(endpoint),
              'unlisted_cells': 'zero on the entire bi-infinite tape',
              'upstream_theorem': 'Boot253.boot_at_prefix330',
              'upstream_source': 'https://github.com/mira-emmy/busy-beaver/blob/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253/coq/tm/Boot253.v'}
    (HERE / 'bootstrap_endpoint.json').write_text(json.dumps(record, indent=2) + '\n')
    print(f'Wrote {len(reached)} invariant configurations, one-row shortcut, and full bootstrap endpoint.')


if __name__ == '__main__':
    main()
