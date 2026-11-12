"""Inventory Python sources without executing them.

Optional independent reproduction requires the pinned ProveIt checkout:
  python3 evidence/census.py --repo /path/to/ProveIt
The saved python_census.json already records the original audit.
"""
import argparse
import ast
import hashlib
import io
import json
import platform
import subprocess
import tokenize
import zipfile
from pathlib import Path

PIN = '203cbef70b358772a43d40ba340209b9ae1d6e32'
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', required=True, type=Path,
                        help='Root of the pinned ProveIt checkout')
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('python_census.json'))
    args = parser.parse_args()
    repo = args.repo.resolve()
    root = repo / 'Logic/PrimitiveRecursiveArithmetic/ConciseIPRA'
    if not (root / 'Artifacts').is_dir():
        parser.error('The supplied checkout has no ConciseIPRA Artifacts directory.')
    observed = subprocess.check_output(
        ['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()
    if observed != PIN:
        parser.error('Expected pinned commit ' + PIN + '; found ' + observed)
    cache, rows, errors = {}, [], []

    def add(path, data, kind):
        sha = hashlib.sha256(data).hexdigest()
        if sha not in cache:
            try:
                normalized = ast.unparse(ast.parse(data)) + '\n'
                tree = ast.parse(normalized)
                cache[sha] = {
                    'sha256': sha,
                    'tokens': sum(t.type not in SKIP for t in tokenize.generate_tokens(
                        io.StringIO(normalized).readline)),
                    'ast_nodes': sum(1 for _ in ast.walk(tree)),
                    'normalized_bytes': len(normalized.encode()),
                    'contains_accept': any(
                        isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
                        and n.func.id == 'print' and n.args
                        and isinstance(n.args[0], ast.Constant)
                        and n.args[0].value == 'ACCEPT' for n in ast.walk(tree)),
                    'contains_json': 'json' in normalized,
                    'packed': any(s in normalized for s in
                                  ['zlib.decompress', 'bz2.decompress',
                                   'lzma.decompress', 'b85decode', 'b64decode']),
                    'source_bytes': len(data),
                }
            except Exception as exc:
                errors.append({'path': path, 'error': str(exc)})
                return
        rows.append({'path': path, 'kind': kind, **cache[sha]})

    for path in sorted((root / 'Artifacts').rglob('*.py')):
        add(str(path.relative_to(root)), path.read_bytes(), 'artifact')
    for path in sorted((root / 'docs/incoming').glob('*.zip')):
        with zipfile.ZipFile(path) as archive:
            for name in archive.namelist():
                if name.endswith('.py'):
                    add(str(path.relative_to(root)) + '::' + name,
                        archive.read(name), 'incoming')
    result = {'python': platform.python_version(), 'snapshot': observed,
              'source_paths': len(rows), 'unique_blobs': len(cache),
              'parse_errors': errors, 'rows': rows}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in
                     ['python', 'snapshot', 'source_paths', 'unique_blobs']}, indent=2))
    print('This is an inventory; eligibility still requires semantic classification.')

if __name__ == '__main__':
    main()
