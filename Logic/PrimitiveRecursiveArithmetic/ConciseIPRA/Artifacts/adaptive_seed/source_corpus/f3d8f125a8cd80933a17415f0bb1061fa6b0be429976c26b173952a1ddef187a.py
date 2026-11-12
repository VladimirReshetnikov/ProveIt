"""Reproduce the pinned archive census without executing source checkers.

Usage: python3 baseline_audit/audit.py
Optional: --manifest PATH --archives DIR --output DIR
The unchanged inherited measurer operates on temporary copies of Python members.
Embedded source ZIPs are included, with paths separated by '!/'.
"""
import argparse
import hashlib
import io
import json
import platform
from pathlib import Path
import tempfile
import zipfile

from source_measure import metrics


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, default=here.parent / 'evidence/repository_snapshot.json')
    parser.add_argument('--archives', type=Path, default=here.parent / 'sources')
    parser.add_argument('--output', type=Path, default=here.parent / 'evidence')
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    archives, rows, failures = [], [], []
    with tempfile.TemporaryDirectory(prefix='ipra-census-') as scratch:
        sample = Path(scratch) / 'sample.py'

        def visit(data, name, depth=0):
            if depth > 8:
                raise ValueError('Unexpected ZIP nesting depth')
            archives.append({'name': name, 'bytes': len(data), 'sha256': digest(data), 'depth': depth})
            with zipfile.ZipFile(io.BytesIO(data)) as archive:
                for member in sorted(archive.namelist()):
                    if member.endswith('/'):
                        continue
                    full = name + '!/' + member
                    raw = archive.read(member)
                    if member.endswith('.zip'):
                        visit(raw, full, depth + 1)
                    elif member.endswith('.py'):
                        sample.write_bytes(raw)
                        try:
                            measured = metrics(sample)
                            measured.pop('core', None)
                            rows.append({'path': full, **measured})
                        except Exception as exc:
                            failures.append({'path': full, 'sha256': digest(raw), 'error': repr(exc)})

        for item in manifest['files']:
            data = (args.archives / item['name']).read_bytes()
            if len(data) != item['size']:
                raise ValueError('Archive size mismatch: ' + item['name'])
            git_sha = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
            if git_sha != item['git_blob_sha1']:
                raise ValueError('Git blob identity mismatch: ' + item['name'])
            visit(data, item['name'])
    result = {
        'commit': manifest['commit'],
        'python': platform.python_version(),
        'measurer_sha256': digest((here / 'source_measure.py').read_bytes()),
        'direct_archives': len(manifest['files']),
        'archive_occurrences_including_embedded': len(archives),
        'python_occurrences': len(rows),
        'distinct_python_sources': len({r['sha256'] for r in rows}),
        'parse_failures': failures,
        'archives': archives,
        'sources': rows,
    }
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'full_inventory.json').write_text(json.dumps(result, indent=2) + '\n')
    summary = {k: v for k, v in result.items() if k not in ('archives', 'sources')}
    print(json.dumps(summary, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
