#!/usr/bin/env python3
"""Reproduce six source-size measurements, without claiming machine validity.

This recovers the unreassociated seed/G source, varies the safe numerical
binder and its local parenthesization, and measures the source trees. It does
not compile or certify any of the exploratory variants. Python 3.10+ with
assertions enabled; no third-party dependencies. Output is JSON on stdout.
"""
from functools import cache
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'portable' / 'source'))
import check_seed_g_source as build


def main():
    assert __debug__ and not sys.flags.optimize, 'Keep assertions enabled'
    source_file = ROOT / 'portable' / 'machine' / 'sites.json'
    raw = source_file.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == build.SOURCE_SHA
    for name, expected in build.PINS.items():
        assert hashlib.sha256((build.ROOT / name).read_bytes()).hexdigest() == expected
    s = build.s
    final = s.tree(json.loads(raw))
    x, yz = s.subtree(final, build.ROTATE)
    y, z = yz
    source = s.replace(final, build.ROTATE, ((x, y), z))
    parent = s.tree(json.loads((build.ROOT / 'inputs/parent225_sites.json').read_text()))
    groups = build.decoder_map(build.read_table(build.ROOT / 'inputs/parent225.k.tm'), parent)

    def q(k):
        assert len(groups[k]) == 1
        return next(iter(groups[k]))

    old = ((q(99), (q(155), q(182))), q(86))

    @cache
    def change(node, replacement):
        if node == old:
            return replacement
        if s.leaf(node):
            return node
        return change(node[0], replacement), change(node[1], replacement)

    measurements = []
    for label, binder in [('Rel', q(155)), ('Eq', q(182)),
                          ('All', (q(98), (q(12), q(86))))]:
        for association, replacement in [
            ('left', ((q(99), (binder, q(182))), q(86))),
            ('right', (q(99), ((binder, q(182)), q(86))))
        ]:
            variant = change(source, replacement)
            measurements.append(dict(binder=label, association=association,
                                     source_metrics=s.metrics(variant)))
    print(json.dumps(dict(
        status='EXPLORATORY_SOURCE_METRICS_ONLY',
        primary_source_sha256=build.SOURCE_SHA,
        undo_rotation_at=build.ROTATE,
        scope='No literal machine construction, runtime certificate, or consistency claim for these variants.',
        measurements=measurements), indent=2))


if __name__ == '__main__':
    main()
