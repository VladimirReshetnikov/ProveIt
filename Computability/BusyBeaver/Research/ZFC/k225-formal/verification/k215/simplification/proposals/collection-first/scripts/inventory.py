#!/usr/bin/env python3
"""Reproduce the pinned K215 source census and domain-guard counterexample.

This is a source audit, not a proof-assistant endpoint check.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

PIN = '6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95'
PROJECTS = ('Computability/BusyBeaver/Lean', 'Logic/FirstOrder/Lean',
            'SetTheory/ZF/Lean', 'SetTheory/BoundedConsistency/Lean')


def guard_counterexample():
    # Objects 0,1 are empty; object 2 has extension {0}; object 3 has {0,1}.
    universe = range(4)
    members = (set(), set(), {0}, {0, 1})
    relation = {(0, 1), (1, 0)}

    def image_collection(a, b):
        support = all(any((x, y) in relation for x in universe)
                      for y in members[b])
        cover = all(not any((x, y) in relation for y in universe)
                    or any((x, y) in relation for y in members[b])
                    for x in members[a])
        return support and cover

    witnesses = [[b for b in universe if image_collection(a, b)]
                 for a in universe]
    image = {y for x in members[2] for y in universe if (x, y) in relation}
    exact = [b for b in universe if members[b] == image]
    functional = all(y == z for x, y in relation for xx, z in relation if xx == x)
    assert all(witnesses) and functional and image == {1} and not exact
    return {'universe': list(universe),
            'membership_extensions': [sorted(s) for s in members],
            'relation': sorted(relation), 'collection_witnesses': witnesses,
            'functional': functional, 'domain_object': 2,
            'image': sorted(image), 'exact_image_objects': exact,
            'conclusion': 'Unguarded global-image collection and functionality do not imply exact image existence.'}


def inventory(repo):
    commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo,
                                     text=True).strip()
    if commit != PIN:
        raise SystemExit(f'Expected snapshot {PIN}; found {commit}')
    modules = {}
    for project in PROJECTS:
        base = repo / project
        if not base.is_dir():
            raise SystemExit(f'Missing source root: {base}')
        for path in base.rglob('*.lean'):
            name = '.'.join(path.relative_to(base).with_suffix('').parts)
            modules[name] = path
    seen, external = set(), set()

    def visit(name):
        if name in seen:
            return
        if name not in modules:
            external.add(name)
            return
        seen.add(name)
        for line in modules[name].read_text().splitlines():
            if line.startswith('import '):
                for child in line[7:].split():
                    visit(child)

    visit('BusyBeaver.ZFC.KEndpoint215')
    files = []
    for name in sorted(seen):
        path = modules[name]
        data = path.read_bytes()
        files.append({'module': name, 'path': str(path.relative_to(repo)),
                      'bytes': len(data), 'lines': len(data.splitlines()),
                      'sha256': hashlib.sha256(data).hexdigest()})
    result = {'commit': commit, 'module_count': len(files),
              'bytes': sum(f['bytes'] for f in files),
              'lines': sum(f['lines'] for f in files),
              'external_import_roots': sorted(external),
              'method': 'Transitive closure of line-start import declarations over four local project roots. Source census, not compilation.',
              'modules': files}
    assert len(files) == 178 and result['bytes'] == 2093112
    assert external == {'Init'}
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    for name, data in [('current_inventory.json', inventory(args.repo.resolve())),
                       ('guard_counterexample.json', guard_counterexample())]:
        (args.output / name).write_text(json.dumps(data, indent=2) + '\n')
    print('PASS: 178 modules, 2,093,112 bytes; domain guard counterexample verified.')


if __name__ == '__main__':
    main()
