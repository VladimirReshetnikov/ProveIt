"""Retrieve the exact source snapshot and statically reproduce its audit.

Network access is optional and only used by this separate corpus audit.
No downloaded Python source is imported or executed.
"""
import ast
import hashlib
import io
import json
from pathlib import Path
import sys
import tokenize
import urllib.request
import zipfile

ROOT = Path(__file__).resolve().parent
IGNORED = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
           tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}


class StripDocstrings(ast.NodeTransformer):
    def clean(self, node):
        self.generic_visit(node)
        if (node.body and isinstance(node.body[0], ast.Expr)
                and isinstance(node.body[0].value, ast.Constant)
                and isinstance(node.body[0].value.value, str)):
            node.body = node.body[1:]
        return node
    visit_Module = clean
    visit_FunctionDef = clean
    visit_AsyncFunctionDef = clean
    visit_ClassDef = clean


def metrics(raw):
    tree = StripDocstrings().visit(ast.parse(raw.decode('utf-8')))
    source = ast.unparse(ast.fix_missing_locations(tree)) + '\n'
    return {'tokens': sum(t.type not in IGNORED for t in
                         tokenize.generate_tokens(io.StringIO(source).readline)),
            'ast': sum(1 for _ in ast.walk(tree)), 'bytes': len(source.encode())}


def main():
    manifest = json.loads((ROOT / 'evidence/source_snapshot.json').read_text())
    retained = json.loads((ROOT / 'evidence/corpus_metrics.json').read_text())
    expected = {r['sha256']: r for r in retained['rows']}
    cache = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / '.audit-cache'
    cache.mkdir(parents=True, exist_ok=True)
    rows = []
    def inspect(blob, path):
        with zipfile.ZipFile(io.BytesIO(blob)) as archive:
            for name in archive.namelist():
                if name.endswith('/'):
                    continue
                if name.endswith('.py'):
                    raw = archive.read(name)
                    sha = hashlib.sha256(raw).hexdigest()
                    measured = metrics(raw)
                    if sha not in expected:
                        raise ValueError('Unrecorded source: ' + path + '!' + name)
                    if any(measured[k] != expected[sha][k] for k in measured):
                        raise ValueError('Metric mismatch: ' + path + '!' + name)
                    rows.append({'path': path + '!' + name, 'sha256': sha,
                                 'classified_complete': expected[sha]['looks_complete'], **measured})
                elif name.endswith('.zip'):
                    inspect(archive.read(name), path + '!' + name)
    for entry in manifest['files']:
        path = cache / entry['name']
        if not path.exists():
            url = entry['download_url'].replace('/main/', '/' + manifest['commit'] + '/')
            path.write_bytes(urllib.request.urlopen(url, timeout=120).read())
        raw = path.read_bytes()
        blob_sha = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        if len(raw) != entry['size'] or blob_sha != entry['sha']:
            raise ValueError('Archive identity mismatch: ' + entry['name'])
        inspect(raw, entry['name'])
    candidates = [r for r in rows if r['classified_complete']]
    envelope = {k: min(r[k] for r in candidates) for k in ('tokens', 'ast', 'bytes')}
    result = {'commit': manifest['commit'], 'archives': len(manifest['files']),
              'python_occurrences_with_nested_archives': len(rows),
              'distinct_python_sources': len({r['sha256'] for r in rows}),
              'coordinate_envelope': envelope,
              'classification': 'Reproduced manual source-role classification by pinned content hash.',
              'all_passed': True}
    (ROOT / 'evidence/corpus_reproduction.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
