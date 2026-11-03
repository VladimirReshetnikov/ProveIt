#!/usr/bin/env python3
"""Read-only source-import plan for a fresh-provider trace75 reverse replay.

This inventories direct imports only. It is not a Lean execution or a proof
that the selected provider's complete transitive ancestry is source-coherent.
"""
import hashlib
import json
import re
import sys
from pathlib import Path

if sys.flags.optimize:
    raise SystemExit("optimized Python refused")

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BASE = Path('/tmp/trace75-fresh-rebuild-yn60cw_0/lib')
PACKAGE = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
CORE = LEAN.parent.parent / 'lib/lean'
PARENT = ROOT / 'research/trace75-fresh-provider-rebuild/observations/attempt01/result.json'

STAGES = [
    ('Trace75GenericCarrier', 'trace75-generic-carrier-prototype'),
    ('Trace75SeedOffset', 'trace75-seed-offset-prototype'),
    ('Trace75UnscaledReverseData', 'trace75-unscaled-reverse-data-prototype'),
    ('Trace75OldTraceMap', 'trace75-old-trace-map-prototype'),
    ('Trace75OldTraceOutput', 'trace75-old-trace-output-prototype'),
    ('Trace75PositiveTraceShift', 'trace75-positive-trace-shift-prototype'),
    ('Trace75NaturalTraceShift', 'trace75-natural-trace-shift-prototype'),
    ('Trace75OldTracePositiveMap', 'trace75-old-trace-positive-map-prototype'),
    ('Trace75OldTracePartsJoin', 'trace75-old-trace-parts-join-prototype'),
    ('Trace75NaturalPartsBinding', 'trace75-natural-parts-binding-prototype'),
    ('Trace75UnscaledReverseGraph', 'trace75-unscaled-reverse-graph-prototype'),
    ('Trace75PackingReverseGraph', 'trace75-packing-reverse-graph-prototype'),
    ('Trace75BFSHaltGraph', 'trace75-bfs-halt-graph-prototype'),
]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def resolve(name):
    rel = Path(name.replace('.', '/') + '.olean')
    for root in (BASE, PACKAGE, CORE):
        p = root / rel
        if p.is_symlink() and not p.is_file():
            raise RuntimeError('dangling import shadow: ' + str(p))
        if p.is_file():
            return {'path': str(p), 'resolved': str(p.resolve(strict=True)),
                    'sha256': digest(p), 'kind': 'project' if root == BASE else 'outside'}
    raise RuntimeError('unresolved direct import: ' + name)


def main():
    parent = json.loads(PARENT.read_text())
    if parent.get('status') != 'PASS' or Path(parent['output_root']) / 'lib' != BASE:
        raise RuntimeError('fresh trace75 parent mismatch')
    names = [name for name, _ in STAGES]
    if len(set(names)) != len(names):
        raise RuntimeError('duplicate stage')
    completed = set()
    stages = []
    for name, folder in STAGES:
        source = ROOT / 'research' / folder / (name + '.lean')
        if (BASE / (name + '.olean')).exists():
            raise RuntimeError('stage already shadows baseline: ' + name)
        imports = re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$', source.read_text(), re.M)
        if not imports:
            raise RuntimeError('empty direct-import list: ' + name)
        direct = {}
        for dep in imports:
            if dep in names:
                if dep not in completed:
                    raise RuntimeError('stage import before producer: ' + name + ' -> ' + dep)
                direct[dep] = {'kind': 'stage'}
            else:
                direct[dep] = resolve(dep)
        stages.append({'module': name, 'source': str(source), 'source_sha256': digest(source),
                       'imports': imports, 'direct': direct})
        completed.add(name)
    result = {'status': 'PASS', 'scope': 'direct source-import plan only; no Lean replay, '
              'serialized closure or complete ancestry verification', 'base': str(BASE),
              'parent': str(PARENT), 'parent_sha256': digest(PARENT),
              'planner_sha256': digest(Path(__file__)), 'stages': stages}
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
