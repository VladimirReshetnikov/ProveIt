"""Recheck archive identities and all Python-source measurements offline.

Semantic classification of complete checkers is the written audit, not a
heuristic implemented here. The recorded measurements are checked by hash.
"""
from pathlib import Path
import hashlib
import io
import json
import runpy
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parent


def main():
    measure = runpy.run_path(str(ROOT / 'reference/source_measure.py'))['metrics']
    manifest = json.loads((ROOT / 'evidence/source_manifest.json').read_text())
    recorded = json.loads((ROOT / 'evidence/baseline_source_metrics.json').read_text())
    recorded += json.loads((ROOT / 'evidence/nested_source_metrics.json').read_text())
    expected = {row['sha256']: (row['tokens'], row['ast'], row['bytes']) for row in recorded}
    actual = {}
    counts = {'direct_python_occurrences': 0, 'nested_python_occurrences': 0}
    def scan(data, nested, temp):
        with zipfile.ZipFile(io.BytesIO(data)) as archive:
            for item in archive.infolist():
                if item.is_dir():
                    continue
                if item.filename.endswith('.py'):
                    blob = archive.read(item)
                    digest = hashlib.sha256(blob).hexdigest()
                    counts['nested_python_occurrences' if nested else 'direct_python_occurrences'] += 1
                    if digest not in actual:
                        path = temp / (digest + '.py')
                        path.write_bytes(blob)
                        metrics = measure(path)
                        actual[digest] = (metrics['normalized_tokens'], metrics['ast_nodes'], metrics['normalized_bytes'])
                elif item.filename.endswith('.zip') and not nested:
                    scan(archive.read(item), True, temp)
    with tempfile.TemporaryDirectory() as tmp:
        for row in manifest['archives']:
            data = (ROOT / 'sources' / row['name']).read_bytes()
            if len(data) != row['size'] or hashlib.sha256(data).hexdigest() != row['sha256']:
                raise ValueError('Archive identity mismatch: ' + row['name'])
            git_blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
            if git_blob != row['git_blob']:
                raise ValueError('Git blob mismatch: ' + row['name'])
            scan(data, False, Path(tmp))
    for digest, values in expected.items():
        if actual.get(digest) != values:
            raise ValueError('Source measurement mismatch: ' + digest)
    for row in manifest['inherited_appendices']:
        if hashlib.sha256((ROOT / row['local']).read_bytes()).hexdigest() != row['sha256']:
            raise ValueError('Inherited appendix changed: ' + row['local'])
    receipt = {'result': 'PASS', 'archives': len(manifest['archives']), **counts,
               'distinct_combined_python_sources': len(actual),
               'recorded_distinct_sources_verified': len(expected),
               'scope': 'Archive bytes and source metrics; complete-checker classification is a written audit.'}
    (ROOT / 'evidence/source_reproduction.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
