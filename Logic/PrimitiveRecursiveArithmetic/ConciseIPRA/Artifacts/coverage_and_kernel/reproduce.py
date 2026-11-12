"""Remeasure frozen sources and reproduce the finite implementation evidence.

No network and no third-party Python dependencies are required.
The mathematical metatheorems rely on the written proofs, not these tests.
"""
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from measure import metrics, runtime

ROOT = Path(__file__).resolve().parent
FIELDS = ('sha256', 'raw_bytes', 'normalized_bytes', 'tokens', 'ast_nodes',
          'gzip9_raw_bytes', 'gzip9_normalized_bytes')


def run(relative):
    process = subprocess.run([sys.executable, str(ROOT / relative)],
                             cwd=ROOT, text=True, capture_output=True)
    if process.returncode:
        print(process.stdout + process.stderr)
        raise SystemExit(process.returncode)
    return json.loads(process.stdout)


def main():
    recorded = json.loads((ROOT / 'evidence/metrics.json').read_text())
    for row in recorded['programs']:
        path = ROOT / row['path']
        raw = path.read_bytes()
        actual = metrics(raw)
        for key in FIELDS:
            if key in row and actual[key] != row[key]:
                raise ValueError(f'Measurement mismatch: {row["path"]}, {key}')
        compressed = path.with_suffix(path.suffix + '.gz')
        if compressed.exists() and compressed.read_bytes() != gzip.compress(
                raw, compresslevel=9, mtime=0):
            raise ValueError('Compressed stream mismatch: ' + row['path'])

    corpus = json.loads((ROOT / 'evidence/corpus_metrics.json').read_text())
    for row in corpus['rows']:
        raw = (ROOT / 'evidence/source_corpus' / (row['sha256'] + '.py')).read_bytes()
        if hashlib.sha256(raw).hexdigest() != row['sha256']:
            raise ValueError('Frozen source identity mismatch')
        if 'parse_error' in row:
            try:
                metrics(raw)
            except (SyntaxError, UnicodeDecodeError, ValueError):
                continue
            raise ValueError('Expected source parse failure')
        actual = metrics(raw)
        if any(actual[k] != row[k] for k in FIELDS):
            raise ValueError('Frozen source measurement mismatch: ' + row['sha256'])

    checks = run('tests/verify_compositions.py')
    arithmetic = run('tests/check_coverage.py')
    (ROOT / 'evidence/coverage_diagnostics.json').write_text(
        json.dumps(arithmetic, indent=2) + '\n')
    receipt = {'status': 'PASS', 'runtime': runtime(),
               'remeasured_complete_profiles': len(recorded['programs']),
               'remeasured_frozen_sources': len(corpus['rows']),
               'checker_checks': checks,
               'arithmetic_counts': arithmetic['counts'],
               'arithmetic_controls': len(arithmetic['targeted_controls']),
               'formal_metatheory_checked_by_proof_assistant': False}
    (ROOT / 'evidence/reproduction.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
