#!/usr/bin/env python3
"""Check the saved compact-proof publication, without invoking proof tools."""
from pathlib import Path
import argparse
import hashlib
import json
import re
from urllib.parse import unquote


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, required=True)
    ap.add_argument('--evidence', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    a = ap.parse_args()
    repo, evidence = a.repo.resolve(), a.evidence.resolve()
    assert not a.output.exists(), 'Keep earlier review receipts'
    read = lambda p: json.loads(p.read_text())
    result = read(evidence / 'actual/result.json')
    assert result['status'] == 'PASS_INCREMENTAL_ENDPOINTS_FOCUSED_KERNEL'
    plan = read(evidence / 'actual/plan.json')
    assert len(plan['order']) == 237 and len(set(plan['order'])) == 237
    assert set(plan['order']) == set(plan['modules'])
    reuse = read(evidence / 'actual/reuse.json')
    affected = result['recompiled']
    assert len(affected) == 7 and len(reuse) == 230
    assert set(affected).isdisjoint(reuse) and set(affected) | set(reuse) == set(plan['order'])
    ledger = read(evidence / 'source-bindings.json')['files']
    for name, row in ledger.items():
        p = repo / name
        assert sha(p) == row['sha256'] and p.stat().st_size == row['bytes']
    closed = {}
    for name in affected:
        record = read(evidence / 'actual/records' / (name + '.json'))
        attempt = evidence / 'actual/attempts' / name
        assert record == read(attempt / 'record.json')
        assert record['status'] == 'PASS' and record['exit_code'] == 0
        assert record['post_inputs_unchanged'] and record['assumption_gate_passed']
        source = Path(plan['modules'][name]['source'])
        assert sha(source) == sha(attempt / source.name) == record['source_sha256']
        log = attempt / 'output.log'
        assert sha(log) == record['output_sha256']
        assert record['argv'][1:] == [*plan['flags'], '-w', '-deprecated,-notation-overridden', plan['modules'][name]['target']]
        closed[name] = log.read_text().count('Closed under the global context')
        if name in ('K215F.DomRho8', 'K215F.Correct215', 'K215F.CorrectDense215'):
            assert closed[name] == 2 and 'Axioms:' not in log.read_text()
    kernel = read(evidence / 'actual/kernel/record.json')
    assert kernel['exit_code'] == 0 and kernel['post_inputs_unchanged']
    assert kernel['argv'][1:] == [*plan['flags'], '-silent', '-o', 'K215F.DomRho8']
    klog = evidence / 'actual/kernel/output.log'
    assert sha(klog) == kernel['output_sha256']
    assert '* Axioms: <none>' in klog.read_text()
    meta = read(evidence / 'metadata-update.json')
    assert sum(row['literal_replacements'] for row in meta['files']) == 3
    for row in meta['files']:
        assert sha(repo / row['path']) == row['after_sha256']
        assert sha(evidence / row['history']) == row['before_sha256']
    generation = read(evidence / 'actual/regeneration215.json')
    kf = repo / 'Computability/BusyBeaver/Research/ZFC/k225-formal'
    current_generation = read(kf / 'rocq/rocq-extension/coq/regeneration215.json')
    assert generation == current_generation
    hashes = generation['generated_source_sha256']
    assert len(hashes) == 42
    for name, digest in hashes.items():
        assert sha(kf / 'rocq/rocq-extension/coq/215' / name) == digest
    links = []
    for target in re.findall(r'\]\(([^)]+)\)', (evidence / 'README.md').read_text()):
        if '://' in target or target.startswith('#'):
            continue
        path = unquote(target.split('#', 1)[0])
        assert (evidence / path).exists(), target
        links.append(target)
    publication = read(evidence / 'publication.json')
    assert sha(evidence / 'actual/result.json') == publication['result_sha256']
    assert sha(evidence / 'source-bindings.json') == publication['source_ledger_sha256']
    assert sha(evidence / 'history.tar.gz') == publication['history_sha256']
    files = {str(p.relative_to(evidence)): {'sha256': sha(p), 'bytes': p.stat().st_size}
             for p in sorted(evidence.rglob('*')) if p.is_file()}
    receipt = {'status': 'PASS_SAVED_PUBLICATION_CURRENT_SOURCES',
               'scope': 'Read-only saved records, logs, current source/metadata and links; no compiler or live object/kernel replay.',
               'fresh_modules': 7, 'baseline_reused_modules': 230, 'closed_reports': closed,
               'regenerated_sources': 42, 'readme_links': links,
               'file_count_before_this_receipt': len(files),
               'bytes_before_this_receipt': sum(p['bytes'] for p in files.values()), 'files': files}
    a.output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k:v for k,v in receipt.items() if k not in ('files', 'readme_links')}, indent=2))


if __name__ == '__main__':
    main()
