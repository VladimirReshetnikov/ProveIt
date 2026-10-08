#!/usr/bin/env python3
"""Check that the staged quantitative port is the Gowers density import closure.

This is a source dependency check, not a Lean proof or a theorem-level
minimality claim. An optional module argument prints an import path from the
density conclusion, explaining why that module belongs to the staged port.
"""
from collections import deque
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[3]
SOURCE = ROOT / 'lib/openai-math/lean'
MANIFEST = SOURCE.parent / 'quantitative-port-manifest.json'


def main():
    manifest = json.loads(MANIFEST.read_text())
    target = manifest['target']
    parent = {target: None}
    queue = deque([target])
    while queue:
        module = queue.popleft()
        source = SOURCE.joinpath(*module.split('.')).with_suffix('.lean')
        if not source.exists():
            raise SystemExit(f'Missing dependency source: {source}')
        for dependency in re.findall(r'^import\s+(\S+)', source.read_text(), re.M):
            if dependency.startswith('OAI.') and dependency not in parent:
                parent[dependency] = module
                queue.append(dependency)
    listed = {entry['module'] for entry in manifest['modules']}
    upstream = {module for module in parent if module.startswith('OAI.Combinatorics.')}
    if listed != upstream:
        raise SystemExit(f'Manifest mismatch: unused={sorted(listed - upstream)}, '
                         f'unlisted={sorted(upstream - listed)}')
    excluded = {entry['module'] for entry in manifest['scope']['excluded']}
    if excluded.intersection(parent):
        raise SystemExit('Excluded reciprocal branch remains in the import closure')
    for module in excluded:
        if SOURCE.joinpath(*module.split('.')).with_suffix('.lean').exists():
            raise SystemExit(f'Excluded module is still vendored: {module}')
    if manifest['upstream_closure_modules'] != len(listed):
        raise SystemExit('Stale manifest module count')
    print(f'Gowers Theorem 1.3 density route: {len(listed)} upstream modules and '
          f'{len(parent) - len(listed)} compatibility modules.')
    print('Reciprocal-only modules excluded. This does not certify Lean proofs '
          'or minimal theorem-level dependencies.')
    for requested in sys.argv[1:]:
        if requested not in parent:
            raise SystemExit(f'Not a density dependency: {requested}')
        path = []
        current = requested
        while current is not None:
            path.append(current)
            current = parent[current]
        print('\n'.join(reversed(path)))


if __name__ == '__main__':
    main()
