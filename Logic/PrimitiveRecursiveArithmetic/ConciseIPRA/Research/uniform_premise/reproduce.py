"""Verify the delivered manifest, measurements and fixed proof controls offline."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
import measure
import verify


def main():
    manifest = ROOT / 'MANIFEST.json'
    if not manifest.is_file():
        raise SystemExit('MANIFEST.json is missing')
    entries = json.loads(manifest.read_text())['files']
    wrong = []
    for row in entries:
        path = ROOT / row['path']
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != row['sha256']:
            wrong.append(row['path'])
    if wrong:
        raise SystemExit('Manifest mismatch: ' + ', '.join(wrong))
    result = measure.measurements()
    if result['frozen_mismatches']:
        raise SystemExit('Frozen corpus measurement mismatch; exact counts use the documented Python/zlib versions')
    stored = json.loads((ROOT / 'evidence/checker_metrics.json').read_text())
    if result['rows'] != stored['rows']:
        raise SystemExit('Delivered program measurement mismatch')
    checked = verify.verify(ROOT)
    if checked['mismatches']:
        raise SystemExit('Proof fixture or mutation mismatch')
    spec = importlib.util.spec_from_file_location('named_producer', ROOT / 'tests/producer.py')
    producer = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(producer)
    regenerated = producer.build_cases()
    failures = [case['name'] for case in regenerated
                if verify.check(ROOT / 'code/checker.py', case['packet'], False) != case['accept']]
    if failures:
        raise SystemExit('Regenerated producer mismatch: ' + ', '.join(failures))
    print(json.dumps({'manifest_files': len(entries), 'frozen_sources': result['frozen_source_count'],
                      'cli_checks': checked['ordinary_checks'], 'mutation_checks': checked['mutation_checks'],
                      'regenerated_core_cases': len(regenerated), 'mismatches': 0}, indent=2))


if __name__ == '__main__':
    main()
