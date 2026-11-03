#!/usr/bin/env python3
"""Inspect added 94-graph model object headers against the compact rebuild cone."""
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import time

HERE = Path(__file__).resolve().parent
D = HERE.parents[1]
B = D / 'research/ordinary12-ipra-bridge'
INVENTORY = B / 'compact12-ipra-all-project-import-inventory/observations/attempt01/result.json'
CONE = B / 'compact12-ipra-expanded-cone-preflight/result-v2.json'
MODEL = D / 'research/ordinary12-sum-squares-model-bridge/observations/attempt01/terminal.json'
HELPER = B / 'compact12-ipra-all-project-import-inventory/ReadObjectImports.lean'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
OUT = HERE / 'observations/attempt01'
EXPECTED = {
    'inventory': 'bf812db57d68117d47d3df792e4a0d6879019d442c4f0f2b0fbef8b861f363f2',
    'cone': '35fce2dd6720ca1f2db8c39e42ad099f5653bf6b12939fcb77db3fd0fa252ed4',
}

def digest(p):
    return sha256(Path(p).read_bytes()).hexdigest()

def available_kib():
    for line in Path('/proc/meminfo').read_text().splitlines():
        if line.startswith('MemAvailable:'):
            return int(line.split()[1])
    raise RuntimeError('MemAvailable not found')

def lean_pids():
    found = []
    for p in Path('/proc').iterdir():
        if not p.name.isdigit():
            continue
        try:
            exe = (p / 'exe').resolve(strict=True)
        except (OSError, RuntimeError):
            continue
        if exe == LEAN.resolve(strict=True):
            found.append(int(p.name))
    return sorted(found)

def closure(root, graph):
    seen, outside, todo = set(), set(), [root]
    while todo:
        x = todo.pop()
        if x in seen or x in outside:
            continue
        if x not in graph:
            outside.add(x)
            continue
        seen.add(x)
        todo.extend(graph[x])
    return seen, outside

def main():
    if OUT.exists():
        raise RuntimeError('refusing to overwrite an observation')
    if digest(INVENTORY) != EXPECTED['inventory'] or digest(CONE) != EXPECTED['cone']:
        raise RuntimeError('prior selected-graph pin mismatch')
    inv = json.loads(INVENTORY.read_text())
    cone = json.loads(CONE.read_text())
    model = json.loads(MODEL.read_text())
    if not (inv['complete'] and inv['overlay_unchanged'] and inv['omitted_unchanged'] and
            model['exit_code'] == 0 and model['union_unchanged'] and model['guards_unchanged']):
        raise RuntimeError('prior observation is incomplete')
    selected = {}
    for rel, record in model['union'].items():
        if not rel.endswith('.olean'):
            raise RuntimeError('unexpected selected companion: ' + rel)
        name = rel[:-6].replace('/', '.')
        path = Path(record['resolved'])
        if not path.is_file() or digest(path) != record['sha256']:
            raise RuntimeError('selected object drift: ' + name)
        selected[name] = {'path': str(path), 'sha256': record['sha256']}
    shared = set(selected) & set(inv['objects'])
    if any(selected[m]['sha256'] != inv['objects'][m]['sha256'] for m in shared):
        raise RuntimeError('model union conflicts with inventoried selection')
    extra = set(selected) - set(inv['objects'])
    if len(selected) != 1288 or len(shared) != 1252 or len(extra) != 36:
        raise RuntimeError('selected graph shape changed')
    top = Path(model['command'][-1])
    if not top.is_file() or digest(top) != model['object_sha256']:
        raise RuntimeError('94 model object drift')
    objects = {m: selected[m] for m in extra}
    objects['SumSquaresModelIff'] = {'path': str(top), 'sha256': model['object_sha256']}
    pins = {'inventory': digest(INVENTORY), 'cone': digest(CONE), 'model': digest(MODEL),
            'helper': digest(HELPER), 'scanner': digest(__file__)}
    graph = {m: list(ds) for m, ds in inv['imports'].items()}
    OUT.mkdir(parents=True)
    names = sorted(objects)
    batches = []
    for offset in range(0, len(names), 16):
        group = names[offset:offset+16]
        memory = available_kib()
        existing = lean_pids()
        if memory < 8 * 1024 * 1024 or len(existing) >= 2:
            raise RuntimeError('resource guard rejected header scan')
        command = [str(LEAN), '-M3000', '-j1', '-DElab.async=false', '--run', str(HELPER)]
        command.extend(objects[m]['path'] for m in group)
        start = time.monotonic()
        result = subprocess.run(command, capture_output=True, text=True, timeout=60)
        elapsed = time.monotonic() - start
        n = offset // 16
        (OUT / f'batch-{n:02d}.stdout').write_text(result.stdout)
        (OUT / f'batch-{n:02d}.stderr').write_text(result.stderr)
        batches.append({'names': group, 'command': command, 'exit_code': result.returncode,
                        'elapsed_seconds': round(elapsed, 3), 'available_kib': memory,
                        'existing_lean_pids': existing})
        if result.returncode or result.stderr:
            raise RuntimeError('object-header reader failed')
        path_to_name = {objects[m]['path']: m for m in group}
        current = None
        for line in result.stdout.splitlines():
            if line.startswith('BEGIN '):
                if current is not None or line[6:] not in path_to_name:
                    raise RuntimeError('unexpected BEGIN: ' + line)
                current = path_to_name[line[6:]]
                graph[current] = []
            elif line.startswith('IMPORT ') and current is not None:
                graph[current].append(line[7:])
            elif line == 'END' and current is not None:
                current = None
            else:
                raise RuntimeError('unexpected reader output: ' + line)
        if current is not None or any(m not in graph for m in group):
            raise RuntimeError('incomplete header output')
    if any(digest(x['path']) != x['sha256'] for x in selected.values()) or digest(top) != model['object_sha256']:
        raise RuntimeError('selected object changed during scan')
    if pins != {'inventory': digest(INVENTORY), 'cone': digest(CONE), 'model': digest(MODEL),
                'helper': digest(HELPER), 'scanner': digest(__file__)}:
        raise RuntimeError('input changed during scan')
    candidates = set(cone['topological_candidate'])
    roots = ['SumSquaresModelIff', 'CompactBytePortsModelIff', 'FreeJSumSquares',
             'CompactFourPortByteAssembly2']
    root_results = {}
    for root in roots:
        ancestors, outside = closure(root, graph)
        root_results[root] = {'selected_ancestors': sorted(ancestors),
                              'candidate_ancestors': sorted(ancestors & candidates),
                              'outside_selected_graph': sorted(outside)}
    output = {'pins': pins, 'added_objects': objects, 'added_imports': {m: graph[m] for m in sorted(objects)},
              'shared_hashes_match': len(shared), 'batches': batches, 'roots': root_results,
              'scope': 'serialized selected-project headers only; package and dynamic ancestry inherited'}
    (OUT / 'result.json').write_text(json.dumps(output, indent=2, sort_keys=True) + '\n')
    print(json.dumps({root: {'selected': len(row['selected_ancestors']),
                             'candidates': len(row['candidate_ancestors']),
                             'outside': len(row['outside_selected_graph'])}
                      for root, row in root_results.items()}, sort_keys=True))

if __name__ == '__main__':
    main()
