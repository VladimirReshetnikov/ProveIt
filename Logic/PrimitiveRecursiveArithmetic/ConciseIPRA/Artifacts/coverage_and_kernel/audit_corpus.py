"""Static corpus audit. No inspected Python source is executed.

Usage: python3 audit_corpus.py /path/to/ProveIt/docs/drafts
The exact commit and Git blob identities are recorded in snapshot.json.
Source bytes are deduplicated by SHA-256, including nested ZIP members.
"""
import hashlib
import io
import json
from pathlib import Path
import sys
import zipfile
from measure import metrics, runtime

ROOT = Path(__file__).resolve().parent


def main():
    source_dir = Path(sys.argv[1])
    snapshot = json.loads((ROOT / 'evidence/snapshot.json').read_text())
    occurrences = []
    archives = []
    sources = {}
    visited = set()

    def inspect(raw, location):
        sha = hashlib.sha256(raw).hexdigest()
        archives.append({'location': location, 'sha256': sha})
        if sha in visited:
            return
        visited.add(sha)
        with zipfile.ZipFile(io.BytesIO(raw)) as z:
            for name in z.namelist():
                if name.endswith('/'):
                    continue
                if name.endswith('.zip'):
                    inspect(z.read(name), location + '!' + name)
                elif name.endswith('.py'):
                    data = z.read(name)
                    key = hashlib.sha256(data).hexdigest()
                    where = location + '!' + name
                    occurrences.append({'sha256': key, 'location': where})
                    if key not in sources:
                        try:
                            row = metrics(data)
                        except (SyntaxError, UnicodeDecodeError, ValueError) as error:
                            row = {'sha256': key, 'parse_error': str(error)}
                        row['locations'] = []
                        sources[key] = row
                        (ROOT / 'evidence/source_corpus' / (key + '.py')).write_bytes(data)
                    sources[key]['locations'].append(where)

    for entry in snapshot['files']:
        raw = (source_dir / entry['name']).read_bytes()
        git_sha = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        if len(raw) != entry['size'] or git_sha != entry['sha']:
            raise ValueError('Archive identity mismatch: ' + entry['name'])
        inspect(raw, entry['name'])
    rows = sorted(sources.values(), key=lambda r: (r.get('normalized_bytes', 10**9), r['sha256']))
    boundary = [r for r in rows if 'parse_error' not in r and
                (r['normalized_bytes'] <= 554 or r['tokens'] <= 262 or r['ast_nodes'] <= 291)]
    result = {'commit': snapshot['commit'], 'runtime': runtime(),
              'outer_archives': len(snapshot['files']),
              'distinct_archives': len(visited),
              'python_occurrences': len(occurrences),
              'distinct_python_sources': len(rows),
              'boundary_sources_to_classify': len(boundary), 'rows': rows}
    (ROOT / 'evidence/corpus_metrics.json').write_text(json.dumps(result, indent=2) + '\n')
    (ROOT / 'evidence/boundary_sources.json').write_text(json.dumps(boundary, indent=2) + '\n')
    (ROOT / 'evidence/archive_manifest.json').write_text(json.dumps(archives, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'rows'}, indent=2))


if __name__ == '__main__':
    main()
