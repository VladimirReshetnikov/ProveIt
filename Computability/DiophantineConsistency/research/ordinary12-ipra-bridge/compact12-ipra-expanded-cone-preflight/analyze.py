#!/usr/bin/env python3
"""Compute a conservative serialized-import rebuild cone for compact/iPRA."""
from collections import Counter
from hashlib import sha256
import heapq
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
INPUT = HERE.parent / 'compact12-ipra-all-project-import-inventory/observations/attempt01/result.json'
MANIFEST = HERE.parent / 'compact12-ipra-integration-build/observations/attempt01/manifest.json'
PINS = HERE.parent / 'compact12-ipra-coherent-rebuild-plan/pins.json'
OUT = HERE / 'result-v2.json'
SOURCE_ROOTS = [
    'Computability/DiophantineConsistency/Lean',
    'Computability/BusyBeaver/Lean',
    'Logic/Interpretability/ZFCinPA/Lean',
    'Logic/Interpretability/PAHF/Lean',
    'SetTheory/BoundedConsistency/Lean',
    'Logic/FirstOrder/Lean',
    'SetTheory/ZF/Lean',
]

def digest(p):
    return sha256(Path(p).read_bytes()).hexdigest()

def closure(roots, graph):
    seen, todo = set(), list(roots)
    while todo:
        x = todo.pop()
        if x in seen:
            continue
        if x not in graph:
            raise RuntimeError(f'missing selected object header: {x}')
        seen.add(x)
        todo.extend(graph[x] - seen)
    return seen

def main():
    if OUT.exists():
        raise RuntimeError('refusing to overwrite observation')
    scan_hash = digest(INPUT)
    scan = json.loads(INPUT.read_text())
    manifest = json.loads(MANIFEST.read_text())
    pins = json.loads(PINS.read_text())
    if not scan['complete'] or not scan['overlay_unchanged'] or not scan['omitted_unchanged']:
        raise RuntimeError('full import inventory incomplete')
    objects = scan['objects']
    graph = {m: set(xs) & set(objects) for m, xs in scan['imports'].items()}
    roots = ['DiophantineConsistency.IPRAExpressionNative',
             'DiophantineConsistency.HAExpressionAssembly',
             'DiophantineConsistency.AdaptiveEquationSyntax2011',
             'CompactSymbolicModelUnconditionalIff']
    stale = set(scan['stale_nine_selected'])
    omitted = set(scan['dirty_omitted'])
    seeds = set(scan['seeds'])
    per_root = {}
    for root in roots:
        ancestor = closure([root], graph)
        per_root[root] = {'ancestors': sorted(ancestor), 'stale_nine': sorted(ancestor & stale),
                          'omitted': sorted(ancestor & omitted), 'seeds': sorted(ancestor & seeds)}
    endpoint = closure(roots[:3], graph)
    candidate = endpoint & (stale | omitted)
    # Use only recorded project-object edges. A cycle is a hard diagnostic.
    degree = {m: len(graph[m] & candidate) for m in candidate}
    reverse = {m: [] for m in candidate}
    for m in candidate:
        for dep in graph[m] & candidate:
            reverse[dep].append(m)
    queue = [m for m in candidate if degree[m] == 0]
    heapq.heapify(queue)
    order = []
    while queue:
        m = heapq.heappop(queue)
        order.append(m)
        for nxt in reverse[m]:
            degree[nxt] -= 1
            if degree[nxt] == 0:
                heapq.heappush(queue, nxt)
    if len(order) != len(candidate):
        raise RuntimeError('serialized-import graph has a candidate cycle')
    source_rows = {}
    for module in order:
        rel = Path(module.replace('.', '/') + '.lean')
        candidates = [REPO / root / rel for root in SOURCE_ROOTS if (REPO / root / rel).is_file()]
        source = candidates[0] if len(candidates) == 1 else None
        row = {'canonical_candidates': [str(p.relative_to(REPO)) for p in candidates],
               'source_sha256': digest(source) if source else None,
               'source_bytes': source.stat().st_size if source else None,
               'object_path': objects[module]['path'], 'object_sha256': objects[module]['sha256'],
               'object_bytes': Path(objects[module]['path']).stat().st_size,
               'object_imports_in_candidate': sorted(graph[module] & candidate),
               'omitted': objects[module]['omitted']}
        if source:
            text = source.read_text()
            parsed = set()
            for line in text.splitlines():
                match = re.match(r'^\s*import\s+(.+?)\s*$', line.split('--', 1)[0])
                if match:
                    parsed.update(re.findall(r'[A-Za-z_][A-Za-z0-9_\.]*', match.group(1)))
            row['source_selected_imports'] = sorted(parsed & set(objects))
            row['object_selected_imports'] = sorted(graph[module])
            row['selected_imports_match'] = (parsed & set(objects)) == graph[module]
            row['pinned_441_match'] = (pins['modules'][module]['sha256'] == row['source_sha256']
                                       if module in pins['modules'] else None)
        source_rows[module] = row
    stage_modules = []
    for base in ('compact12-ipra-incremental-rebuild-merged',
                 'compact12-ipra-incremental-rebuild-merged-next',
                 'compact12-ipra-incremental-rebuild-merged-batch03'):
        for p in sorted((HERE.parent / base / 'observations').glob('stage-*/terminal.json')):
            row = json.loads(p.read_text())
            ancestors = closure([row['module']], graph)
            stage_modules.append({'module': row['module'], 'index': row['index'],
                                  'stale_nine_ancestors': sorted(ancestors & stale),
                                  'stale_omitted_ancestors': sorted(ancestors & omitted),
                                  'seed_ancestors': sorted(ancestors & seeds)})
    conflict_rows = {}
    for module in sorted(endpoint & seeds):
        rel = module.replace('.', '/') + '.olean'
        conflict_rows[module] = {'selected': objects[module],
                                 'compact_and_nine_sha256': manifest['full_shared_conflicts'][rel]}
    summary = {'endpoint_ancestor_count': len(endpoint),
               'endpoint_stale_nine_count': len(endpoint & stale),
               'endpoint_omitted_count': len(endpoint & omitted),
               'endpoint_seed_count': len(endpoint & seeds),
               'candidate_count': len(candidate),
               'candidate_by_top_namespace': dict(Counter(m.split('.')[0] for m in candidate)),
               'canonical_sources_unique': sum(len(x['canonical_candidates']) == 1 for x in source_rows.values()),
               'canonical_sources_missing': sum(not x['canonical_candidates'] for x in source_rows.values()),
               'canonical_sources_ambiguous': sum(len(x['canonical_candidates']) > 1 for x in source_rows.values()),
               'source_import_mismatches': sum(x.get('selected_imports_match') is False for x in source_rows.values()),
               'existing_object_bytes': sum(x['object_bytes'] for x in source_rows.values()),
               'fifteen_stages_affected': sum(bool(x['stale_nine_ancestors']) for x in stage_modules)}
    result = {'scan_sha256': scan_hash, 'manifest_sha256': digest(MANIFEST), 'pins_sha256': digest(PINS),
              'scope': 'serialized selected-project object graph; current canonical sources are not authenticated historical origins',
              'roots': per_root, 'topological_candidate': order, 'candidate_sources': source_rows,
              'endpoint_conflicting_selected_objects': conflict_rows,
              'rebuilt_stage_ancestry': sorted(stage_modules, key=lambda x: x['index']), 'summary': summary}
    OUT.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(summary, sort_keys=True))

if __name__ == '__main__':
    main()
