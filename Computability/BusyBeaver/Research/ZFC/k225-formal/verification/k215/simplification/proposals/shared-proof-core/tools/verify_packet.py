#!/usr/bin/env python3
"""Read-only integrity verification. This does not run any proof kernel."""
import argparse
import hashlib
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    root = args.root.resolve()
    manifest = json.loads((root / 'manifest.json').read_text())
    for item in manifest['files']:
        path = root / item['path']
        if not path.is_relative_to(root) or not path.is_file():
            raise SystemExit('Missing or invalid path: ' + item['path'])
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != item['sha256'] or path.stat().st_size != item['bytes']:
            raise SystemExit('Content mismatch: ' + item['path'])
    for path in root.rglob('*'):
        if path.is_file() and path.suffix in {'.olean', '.ilean', '.vo', '.vok', '.vos', '.pyc'}:
            raise SystemExit('Unexpected generated object in source packet: ' + str(path))
    metrics = json.loads((root / 'lean_shared/verification/source_metrics.json').read_text())
    assert (metrics['before_bytes'], metrics['after_bytes']) == (42715, 18668)
    assert (metrics['source_mp_nodes_before'], metrics['source_mp_nodes_after']) == (164, 63)
    semantic = json.loads((root / 'semantic_sites/verification/build_result.json').read_text())
    assert semantic['status'] == 'PASS' and len(semantic['records']) == 14
    assert all(r['returncode'] == 0 for r in semantic['records'])
    rocq = json.loads((root / 'rocq_core/evidence/final_receipt.json').read_text())
    candidate = rocq['runs']['candidate']
    assert len(candidate['modules']) == 8
    assert all(r['returncode'] == 0 for r in candidate['modules'])
    assert candidate['coqchk']['returncode'] == 0
    assert sum(r['assumptions_closed_count'] for r in candidate['modules']) == 11
    print(json.dumps({'status': 'PASS', 'checked_files': len(manifest['files']),
                      'source_commit': manifest['source_commit'],
                      'scope': 'SHA-256 integrity and recorded-status consistency only; no kernel executed.'}, indent=2))


if __name__ == '__main__':
    main()
