#!/usr/bin/env python3
"""Recompute the recorded preflight graph from pinned records; do not run Lean."""
from collections import deque
from hashlib import sha256
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BRIDGE = ROOT / 'research/ordinary12-ipra-bridge'
PACKET = ROOT / 'research/ordinary12-sum-squares-endpoint-import-preflight'
if sys.argv[1:] not in ([], ['attempt01'], ['attempt02']):
    raise SystemExit('usage: check.py [attempt01|attempt02]')
attempt = sys.argv[1] if sys.argv[1:] else 'attempt01'
OBS = PACKET / 'observations' / attempt
MODEL = ROOT / 'research/ordinary12-sum-squares-model-bridge/observations/attempt01/terminal.json'
EVIDENCE = {
    'result.json': {
        'attempt01': '73dccb6101fa718925c70b736a622b9cdae124001d7b22f3ccc909a08d9e2cd7',
        'attempt02': 'b15febdf3f77edc4ecdabddb3da2d9bf8735549d28869c4ec18d0669096a45ce',
    }[attempt],
    'batch-00.stdout': '96c3ae0a5e1dd7de409e51b442c95cd43655831147b7bff7e4da1de864d765e0',
    'batch-01.stdout': 'bf7914db89e1a85dc9672fb6992f5bf71425f1feec35c899f6669c2503459a35',
    'batch-02.stdout': 'edba964d09d40b785aec0ce59bfad350502b27de03bd4b62a00b0a33ab1ed248',
}
FILES = {
    'inventory': BRIDGE / 'compact12-ipra-all-project-import-inventory/observations/attempt01/result.json',
    'cone': BRIDGE / 'compact12-ipra-expanded-cone-preflight/result-v2.json',
    'model': MODEL,
    'helper': BRIDGE / 'compact12-ipra-all-project-import-inventory/ReadObjectImports.lean',
    'scanner': PACKET / ('scan-attempt01.py' if attempt == 'attempt01' else 'scan.py'),
}

def require(condition, message):
    if not condition:
        raise SystemExit(message)

def digest(path):
    return sha256(path.read_bytes()).hexdigest()

def read(path):
    return json.loads(path.read_text())

require({name: digest(OBS / name) for name in EVIDENCE} == EVIDENCE, 'captured evidence hash mismatch')
result = read(OBS / 'result.json')
pins_before = {name: digest(path) for name, path in FILES.items()}
require(pins_before == result['pins'], 'recorded input pin mismatch')
inventory = read(FILES['inventory'])
cone = read(FILES['cone'])
model = read(MODEL)
require(inventory['complete'] and inventory['overlay_unchanged'] and inventory['omitted_unchanged'], 'inventory incomplete')
require(model['exit_code'] == 0 and model['union_unchanged'] and model['guards_unchanged'], 'model receipt incomplete')
require(set(inventory['imports']) == set(inventory['objects']), 'inventory import/object keys differ')
selected = {}
for rel, info in model['union'].items():
    require(rel.endswith('.olean'), 'unexpected union file extension')
    name = rel[:-6].replace('/', '.')
    require(name not in selected, 'duplicate normalized selected name')
    path = Path(info['resolved'])
    require(path.is_file() and digest(path) == info['sha256'], 'selected object missing or drifted: ' + name)
    selected[name] = {'path': str(path), 'sha256': info['sha256']}
shared = set(selected).intersection(inventory['objects'])
extra = set(selected).difference(inventory['objects'])
require((len(selected), len(shared), len(extra)) == (1288, 1252, 36), 'unexpected union sizes')
for name in shared:
    require(selected[name]['sha256'] == inventory['objects'][name]['sha256'], 'shared object hash mismatch: ' + name)
require(result['shared_hashes_match'] == len(shared), 'shared count mismatch')
top_path = Path(model['command'][-1])
require(top_path.is_file() and digest(top_path) == model['object_sha256'], 'top object missing or drifted')
expected = {name: selected[name] for name in extra}
expected['SumSquaresModelIff'] = {'path': str(top_path), 'sha256': model['object_sha256']}
require(result['added_objects'] == expected, 'added-object table mismatch')
graph = {name: list(imports) for name, imports in inventory['imports'].items()}
parsed = {}
seen_batch_names = set()
for index, batch in enumerate(result['batches']):
    require(batch['exit_code'] == 0 and batch['available_kib'] >= 8 * 1024 * 1024, 'batch guard/exit mismatch')
    require(len(batch['existing_lean_pids']) < 2, 'batch Lean count guard mismatch')
    require((OBS / f'batch-{index:02d}.stderr').read_bytes() == b'', 'batch stderr not empty')
    names = batch['names']
    require(not (seen_batch_names & set(names)) and len(names) == len(set(names)), 'duplicate batch name')
    seen_batch_names.update(names)
    by_path = {expected[name]['path']: name for name in names}
    require(len(by_path) == len(names), 'duplicate batch object path')
    require(batch['command'][-len(names):] == [expected[name]['path'] for name in names], 'batch command order mismatch')
    current = None
    for line in (OBS / f'batch-{index:02d}.stdout').read_text().splitlines():
        if line.startswith('BEGIN '):
            require(current is None and line[6:] in by_path, 'bad BEGIN')
            current = by_path[line[6:]]
            require(current not in parsed, 'duplicate object record')
            parsed[current] = []
        elif line.startswith('IMPORT ') and current is not None:
            parsed[current].append(line[7:])
        elif line == 'END' and current is not None:
            current = None
        else:
            raise SystemExit('bad record: ' + line)
    require(current is None and all(name in parsed for name in names), 'incomplete batch output')
require(seen_batch_names == set(expected) and set(parsed) == set(expected), 'added header coverage mismatch')
require(parsed == result['added_imports'], 'saved imported headers differ from batch output')
graph.update(parsed)
candidates = set(cone['topological_candidate'])
require(len(candidates) == 425 == len(cone['topological_candidate']), 'unexpected candidate count')
summary = {}
for root, record in result['roots'].items():
    queue = deque([root])
    visited, outside = set(), set()
    while queue:
        name = queue.popleft()
        if name in visited or name in outside:
            continue
        if name not in graph:
            outside.add(name)
        else:
            visited.add(name)
            queue.extend(graph[name])
    require(visited == set(record['selected_ancestors']), 'ancestor mismatch: ' + root)
    require(outside == set(record['outside_selected_graph']), 'outside mismatch: ' + root)
    require(visited & candidates == set(record['candidate_ancestors']) == set(), 'candidate intersection: ' + root)
    require(visited <= set(selected) | {'SumSquaresModelIff'}, 'ancestor outside recorded model union: ' + root)
    require({n.split('.')[0] for n in outside} <= {'Foundation', 'Mathlib', 'Lean', 'Init'}, 'unexpected outside prefix')
    summary[root] = {'model_ancestors': len(visited), 'candidate_intersection': 0, 'outside': len(outside)}
require(set(result['roots']) == {'SumSquaresModelIff', 'CompactBytePortsModelIff', 'FreeJSumSquares', 'CompactFourPortByteAssembly2'}, 'root set mismatch')
for item in selected.values():
    require(digest(Path(item['path'])) == item['sha256'], 'selected object changed while reviewing')
require(digest(top_path) == model['object_sha256'], 'top object changed while reviewing')
require({name: digest(path) for name, path in FILES.items()} == pins_before, 'input changed while reviewing')
require({name: digest(OBS / name) for name in EVIDENCE} == EVIDENCE, 'evidence changed while reviewing')
print(json.dumps(summary, sort_keys=True, indent=2))
