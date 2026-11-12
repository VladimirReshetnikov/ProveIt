"""Optional, portable audit of the pinned thirteen-archive source corpus.

Examples, when this script is at the report package root:
    python3 reproduce_corpus_audit.py --archives /path/to/docs/drafts
    python3 reproduce_corpus_audit.py --archives ./downloaded-drafts --download

The first command is offline. The second downloads missing archives only, using
immutable commit URLs reconstructed from evidence/pinned_sources.json. Existing
archives must already match their Git blob SHA-1 and byte size; mismatches abort.
No Python code from a source archive is executed. ZIPs are read in memory, never
extracted. The driver filter is an inventory aid, not a soundness certificate.
The full comparison includes historical sources in nested archives.

Only the Python standard library is required. CPython/ast.unparse and compression
versions can affect normalized or gzip metrics; content hashes do not depend on
those versions. The original report's minimum attainers were separately read
and reviewed; this script does not automatically certify arbitrary candidates.
"""
import argparse
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import tokenize
import urllib.parse
import urllib.request
import zipfile
import zlib

ROOT = Path(__file__).resolve().parent
REPOSITORY = 'VladimirReshetnikov/ProveIt'
IGNORED = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
           tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}
METRICS = ('raw_bytes', 'normalized_bytes', 'normalized_tokens', 'ast_nodes',
           'gzip9_raw_bytes', 'gzip9_normalized_bytes')


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


def measurements(raw):
    source = raw.decode('utf-8')
    tree = ast.fix_missing_locations(StripDocstrings().visit(ast.parse(source)))
    normal = (ast.unparse(tree) + '\n').encode('utf-8')
    tokens = sum(t.type not in IGNORED for t in
                 tokenize.generate_tokens(io.StringIO(normal.decode()).readline))
    return dict(sha256=hashlib.sha256(raw).hexdigest(), raw_bytes=len(raw),
                normalized_bytes=len(normal), normalized_tokens=tokens,
                ast_nodes=sum(1 for _ in ast.walk(tree)),
                gzip9_raw_bytes=len(gzip.compress(raw, compresslevel=9, mtime=0)),
                gzip9_normalized_bytes=len(gzip.compress(normal, compresslevel=9, mtime=0)),
                driver=('ACCEPT' in source and ('open(0)' in source or 'stdin' in source)))


def git_blob_sha(raw):
    return hashlib.sha1(b'blob ' + str(len(raw)).encode('ascii') + b'\0' + raw).hexdigest()


def verified_bytes(path, row):
    raw = path.read_bytes()
    if len(raw) != row['size'] or git_blob_sha(raw) != row['sha']:
        raise ValueError('Pinned archive mismatch: ' + str(path))
    return raw


def obtain(directory, row, commit, download):
    name = row['name']
    if Path(name).name != name or not name.endswith('.zip'):
        raise ValueError('Expected a plain ZIP filename in pinned metadata')
    path = directory / name
    repository_path = directory / row['path']
    if not path.exists() and repository_path.exists():
        path = repository_path
    immutable_url = ('https://raw.githubusercontent.com/' + REPOSITORY + '/' + commit + '/'
                     + urllib.parse.quote(row['path'], safe='/'))
    if path.exists():
        return verified_bytes(path, row), path, immutable_url
    if not download:
        raise FileNotFoundError(str(path) + ' (supply --download to retrieve missing archives)')
    directory.mkdir(parents=True, exist_ok=True)
    request = urllib.request.Request(immutable_url, headers={'User-Agent': 'iPRA-corpus-audit/1'})
    with urllib.request.urlopen(request, timeout=60) as response:
        raw = response.read(row['size'] + 1)
    if len(raw) != row['size'] or git_blob_sha(raw) != row['sha']:
        raise ValueError('Downloaded content does not match the pinned blob: ' + name)
    temporary = directory / (name + '.part')
    temporary.write_bytes(raw)
    temporary.replace(path)
    return raw, path, immutable_url


def audit(manifest, directory, download=False):
    sources = {}
    archives = set()
    errors = []
    pinned = []
    member_occurrences = 0

    def source(raw, path):
        nonlocal member_occurrences
        member_occurrences += 1
        digest = hashlib.sha256(raw).hexdigest()
        if digest in sources:
            sources[digest]['paths'].append(path)
            return
        try:
            row = measurements(raw)
            row['paths'] = [path]
            sources[digest] = row
        except (UnicodeError, SyntaxError, ValueError, RecursionError) as exc:
            errors.append(dict(path=path, error=type(exc).__name__ + ': ' + str(exc)))

    def archive(raw, path):
        digest = hashlib.sha256(raw).hexdigest()
        if digest in archives:
            return
        archives.add(digest)
        with zipfile.ZipFile(io.BytesIO(raw)) as zipped:
            for item in zipped.infolist():
                if item.filename.endswith('.py'):
                    source(zipped.read(item), path + '!' + item.filename)
                elif item.filename.endswith('.zip'):
                    archive(zipped.read(item), path + '!' + item.filename)

    for entry in manifest['files']:
        raw, local, url = obtain(directory, entry, manifest['commit'], download)
        pinned.append(dict(name=entry['name'], git_blob_sha1=git_blob_sha(raw),
                           sha256=hashlib.sha256(raw).hexdigest(), bytes=len(raw),
                           immutable_url=url))
        archive(raw, entry['name'])
    rows = sorted(sources.values(), key=lambda r: r['sha256'])
    drivers = [row for row in rows if row['driver']]
    minima = {}
    for metric in METRICS:
        value = min(row[metric] for row in drivers)
        minima[metric] = dict(value=value, sources=[
            dict(sha256=row['sha256'], paths=row['paths']) for row in drivers
            if row[metric] == value])
    return dict(commit=manifest['commit'], python=platform.python_version(),
                implementation=platform.python_implementation(),
                zlib_compiled=zlib.ZLIB_VERSION, zlib_runtime=zlib.ZLIB_RUNTIME_VERSION,
                direct_archives=len(pinned), distinct_archives=len(archives),
                python_member_occurrences=member_occurrences, sources=len(rows),
                nominal_checkers=len(drivers), errors=errors, pinned_archives=pinned,
                minima=minima, rows=rows,
                qualification='Driver-filtered minima are not automatic soundness certifications.')


def compare(result, expected):
    actual = {row['sha256']: row for row in result['rows']}
    prior = {row['sha256']: row for row in expected['rows']}
    shared = actual.keys() & prior.keys()
    differences = []
    for digest in sorted(shared):
        delta = {field: {'recorded': prior[digest][field], 'actual': actual[digest][field]}
                 for field in METRICS if prior[digest][field] != actual[digest][field]}
        if delta:
            differences.append(dict(sha256=digest, differences=delta))
    return dict(source_hashes_match=actual.keys() == prior.keys(),
                missing_hashes=sorted(prior.keys() - actual.keys()),
                extra_hashes=sorted(actual.keys() - prior.keys()),
                metric_differences=differences,
                note='AST normalization and compression metrics may change with runtime versions.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, default=ROOT / 'evidence/pinned_sources.json')
    parser.add_argument('--archives', type=Path, required=True,
                        help='Directory containing the 13 ZIP files, or a repository root')
    parser.add_argument('--download', action='store_true', help='Retrieve missing pinned ZIPs')
    parser.add_argument('--output', type=Path, default=Path('recomputed_corpus_audit.json'))
    parser.add_argument('--compare', type=Path, default=ROOT / 'evidence/current_metrics.json')
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    result = audit(manifest, args.archives, args.download)
    if args.compare.exists():
        result['comparison'] = compare(result, json.loads(args.compare.read_text()))
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({
        'commit': result['commit'], 'verified_direct_archives': result['direct_archives'],
        'distinct_archives': result['distinct_archives'],
        'distinct_python_sources': result['sources'], 'nominal_checkers': result['nominal_checkers'],
        'parse_errors': len(result['errors']),
        'nominal_coordinate_minima': {k: v['value'] for k, v in result['minima'].items()},
        'comparison': result.get('comparison')}, indent=2))
    if result['errors']:
        return 1
    if 'comparison' in result and not result['comparison']['source_hashes_match']:
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
