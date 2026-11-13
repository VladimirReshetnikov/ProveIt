"""Reproduce the pinned static source census without executing source code."""
import argparse
import ast
import csv
import gzip
import hashlib
import io
import json
from pathlib import Path
import sys
import tokenize
import zipfile

SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.INDENT,
        tokenize.DEDENT, tokenize.NEWLINE, tokenize.NL, tokenize.COMMENT}


def measure(path, data):
    tree = ast.parse(data)
    normalized = (ast.unparse(tree) + '\n').encode()
    nodes = list(ast.walk(tree))
    calls = [node for node in nodes if isinstance(node, ast.Call)]
    return dict(path=path, sha256_source=hashlib.sha256(data).hexdigest(),
                sha256_normalized=hashlib.sha256(normalized).hexdigest(),
                significant_tokens=sum(t.type not in SKIP for t in
                    tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)),
                ast_nodes=len(nodes), normalized_utf8_bytes=len(normalized),
                print_accept=any(isinstance(n.func, ast.Name) and n.func.id == 'print'
                    and n.args and isinstance(n.args[0], ast.Constant)
                    and n.args[0].value == 'ACCEPT' for n in calls),
                dynamic_source=any(isinstance(n.func, ast.Name)
                    and n.func.id in {'eval', 'exec'} for n in calls),
                labeled_negative=any(x in path.lower() for x in ['rejected', '/negative/']))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', required=True, type=Path)
    parser.add_argument('--source-root', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    rows, errors = [], []

    def add(path, data):
        try:
            rows.append(measure(path, data))
        except Exception as error:
            errors.append(dict(path=path, error=str(error)))

    for record in manifest['files']:
        path = record['path']
        data = (args.source_root / path).read_bytes()
        digest = hashlib.sha256(data).hexdigest()
        if digest != record['sha256'] or len(data) != record['bytes']:
            raise ValueError('Source identity mismatch: ' + path)
        if path.endswith('.zip'):
            with zipfile.ZipFile(io.BytesIO(data)) as archive:
                for name in sorted(archive.namelist()):
                    if name.endswith(('.py', '.py.gz')):
                        source = archive.read(name)
                        if name.endswith('.gz'):
                            source = gzip.decompress(source)
                        add(path + '!' + name, source)
        else:
            if path.endswith('.gz'):
                data = gzip.decompress(data)
            add(path, data)
    result = dict(pinned_commit=manifest['revision'], python=sys.version,
                  manifest_files_verified=len(manifest['files']),
                  occurrence_count=len(rows),
                  normalized_module_count=len({r['sha256_normalized'] for r in rows}),
                  parse_failures=errors,
                  limitation='Static source census, not a proof of semantic correctness, '
                             'input-contract equivalence, or optimality.',
                  sources=rows)
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'census.json').write_text(json.dumps(result, indent=2) + '\n')
    with (args.output / 'census.csv').open('w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    print(json.dumps({k:v for k,v in result.items() if k != 'sources'}, indent=2))
    if errors:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
