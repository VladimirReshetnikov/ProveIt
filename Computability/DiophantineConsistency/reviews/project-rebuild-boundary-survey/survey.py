#!/usr/bin/env python3
"""Estimate reverse source-import reach; this is not a Lean dependency proof."""
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
STATE = Path('/tmp/pra14-full-transitive-2x6o__to/state.json')
STATE_SHA = '67a9223288a4c5ffb582d70db63d27ad224fd2474c49ce12811f745d673daa91'
MANIFEST = HERE.parent / 'foundation-provider-recovery/input-manifest.json'
MANIFEST_SHA = '491075df9eac57799d21b475527b3b1af3dc81ded58e97a87e1cf6c453dcb13d'
COMPARISON = HERE.parent / 'foundation-provider-recovery/initial-comparison.json'
COMPARISON_SHA = 'f0111e992569499ec3b6bcc057480d3c0de3a8c05b5c8c3a004a1b7570cb3a6b'
FOUNDATION = Path('/tmp/ipra-foundation-rebuild-DqHJmJJe/lib/FormalizedFormalLogic-Foundation')
CHANGED = 'Foundation.FirstOrder.Basic.Semantics.Semantics'

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    assert digest(STATE) == STATE_SHA and digest(MANIFEST) == MANIFEST_SHA
    assert digest(COMPARISON) == COMPARISON_SHA
    state = json.loads(STATE.read_text())
    manifest = json.loads(MANIFEST.read_text())
    comparison = json.loads(COMPARISON.read_text())
    mismatch = [row for row in comparison['rows'] if row['module'] == CHANGED]
    assert len(mismatch) == 1 and mismatch[0]['matches'] is False
    assert mismatch[0]['historical_sha256'] == state['graph']['external_hashes'][CHANGED]
    files = {str(p.relative_to(FOUNDATION)): digest(p) for p in sorted(FOUNDATION.rglob('*')) if p.is_file()}
    assert files == manifest['foundation_archive_files_sha256']
    project_edges = state['graph']['edges']
    assert len(project_edges) == 848
    edges = dict(project_edges)
    foundation_count = 0
    for path in (FOUNDATION / 'Foundation').rglob('*.lean'):
        name = '.'.join(path.relative_to(FOUNDATION).with_suffix('').parts)
        assert name not in edges
        imports = []
        for line in path.read_text().splitlines():
            match = re.match(r'^\s*(?:(?:public|meta)\s+)*import\s+([^\s]+)', line)
            if match:
                imports.append(match.group(1))
        edges[name] = imports
        foundation_count += 1
    def reach(graph):
        reverse = defaultdict(list)
        for module, deps in graph.items():
            for dep in deps:
                reverse[dep].append(module)
        seen, pending = set(), [CHANGED]
        while pending:
            for module in reverse[pending.pop()]:
                if module not in seen:
                    seen.add(module)
                    pending.append(module)
        return seen
    direct_reach = reach(project_edges)
    combined_reach = reach(edges)
    projects = sorted(set(project_edges) & combined_reach)
    foundation = sorted(set(edges) - set(project_edges) & combined_reach)
    receipt = {'status': 'PLANNING_SURVEY', 'ancestor_state_sha256': STATE_SHA,
               'foundation_manifest_sha256': MANIFEST_SHA,
               'comparison_sha256': COMPARISON_SHA, 'changed_seed': CHANGED,
               'historical_project_nodes': len(project_edges),
               'source_scanned_foundation_nodes': foundation_count,
               'project_only_reverse_count': len(direct_reach),
               'combined_project_reverse_count': len(projects),
               'combined_foundation_reverse_count': len(foundation),
               'combined_project_reverse_modules': projects,
               'combined_foundation_reverse_modules': foundation,
               'scope': 'Line-based archived source import scan joined to historical project graph; '
                        'not authenticated old transitive closure, a Lean dependency trace, '
                        'a current endpoint closure or a compatibility proof.'}
    out = HERE / 'receipt.json'
    if out.exists():
        raise RuntimeError('refusing to overwrite receipt')
    out.write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
    print(receipt['status'], len(direct_reach), len(projects), len(foundation), digest(out))

if __name__ == '__main__':
    main()
