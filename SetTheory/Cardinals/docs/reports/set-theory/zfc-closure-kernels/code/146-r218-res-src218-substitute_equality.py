#!/usr/bin/env python3
"""Compose the proved K219 equality replacement with prior source equivalents.

This is a source-only screen. Every accepted input has exactly the pinned
K220 primitive word and both independently resolved ordinal CFGs. Replacing
any literal occurrence of the old equality macro is justified by K219's
all-natural terminating open-tree contract. No state count is certified here.
"""
from pathlib import Path
from functools import lru_cache
import importlib.util, hashlib, json, sys, time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'source_work'))
import rotation_search as r
s = r.s
spec = importlib.util.spec_from_file_location('source219', ROOT / 'baseline219/K219_Construction_2026-10-20/portable/build_source219.py')
eq = importlib.util.module_from_spec(spec)
spec.loader.exec_module(eq)

def main():
    out = ROOT / 'source218/equality_compositions'
    out.mkdir(exist_ok=True, parents=True)
    baseline = json.loads((ROOT / 'baseline220/K220_Construction_2026-10-20/machine/sites220.json').read_text())
    word = [x[1:] for x in baseline]
    graph = s.graph_arithmetic(baseline)[0]
    assert graph == s.graph_intervals(baseline)
    paths = sorted({p for parent in ('source_work', 'root_work', 'machine_work')
                    for p in (ROOT / parent).rglob('*.json')
                    if 'sites' in p.name})
    paths.insert(0, ROOT / 'baseline220/K220_Construction_2026-10-20/machine/sites220.json')
    seen_inputs, seen_outputs, results = set(), {}, []
    skipped = {'non_source_or_word': 0, 'duplicate_input': 0, 'cfg_mismatch': 0, 'no_literal_macro': 0}
    start = time.monotonic()
    for path in paths:
        try:
            rows = json.loads(path.read_text())
            if not isinstance(rows, list) or len(rows) != len(word) or [x[1:] for x in rows] != word:
                skipped['non_source_or_word'] += 1
                continue
        except (ValueError, TypeError, IndexError):
            skipped['non_source_or_word'] += 1
            continue
        raw = s.compact(rows)
        digest = hashlib.sha256(raw).hexdigest()
        if digest in seen_inputs:
            skipped['duplicate_input'] += 1
            continue
        seen_inputs.add(digest)
        if s.graph_arithmetic(rows)[0] != graph or s.graph_intervals(rows) != graph:
            skipped['cfg_mismatch'] += 1
            continue
        tree = s.tree(rows)
        occurrences = []
        def replace(node, prefix=''):
            if node == eq.OLD:
                occurrences.append(prefix)
                return eq.NEW
            if s.leaf(node):
                return node
            return replace(node[0], prefix + '0'), replace(node[1], prefix + '1')
        changed = replace(tree)
        if not occurrences:
            skipped['no_literal_macro'] += 1
            continue
        assert len(occurrences) <= 4
        new_rows = s.sites(changed)
        assert len(new_rows) == 4744
        new_raw = s.compact(new_rows)
        new_digest = hashlib.sha256(new_raw).hexdigest()
        if new_digest in seen_outputs:
            seen_outputs[new_digest]['also_from'].append(str(path.relative_to(ROOT)))
            continue
        folder = out / f'v{len(results):04d}'
        folder.mkdir(exist_ok=True)
        record = {'status': 'PROVED_SOURCE_COMPOSITION_REQUIRES_TABLE',
                  'input': str(path.relative_to(ROOT)), 'input_sha256': digest,
                  'output': str((folder/'sites.json').relative_to(ROOT)),
                  'output_sha256': new_digest, 'replacement_count': len(occurrences),
                  'replaced_paths': occurrences, 'old_metrics': s.metrics(tree),
                  'metrics': s.metrics(changed), 'also_from': []}
        (folder/'sites.json').write_bytes(new_raw)
        seen_outputs[new_digest] = record
        results.append(record)
    for record in results:
        (ROOT / record['output']).with_name('receipt.json').write_text(json.dumps(record, indent=2)+'\n')
    ordered = sorted(results, key=lambda x: (x['metrics']['dag_nodes'], x['metrics']['maximum_zero_run'], x['metrics']['maximum_depth']))
    receipt = {'status': 'SOURCE_COMPOSITION_SCREEN_COMPLETE', 'source_files': len(paths),
               'unique_inputs': len(seen_inputs), 'unique_outputs': len(results),
               'skipped': skipped, 'seconds': time.monotonic()-start, 'results': ordered}
    (out/'summary.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='results'}, indent=2))
    for record in ordered[:20]:
        print(record['output'], record['metrics'], 'replacements', record['replacement_count'])

if __name__ == '__main__':
    main()
