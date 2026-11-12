"""Static, reproducible metrics for the pinned draft archives; executes no draft code."""
import argparse
import ast
import csv
import gzip
import hashlib
import io
import json
import platform
from pathlib import Path
import tokenize
import zipfile

IGNORED = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL,
           tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT,
           tokenize.ENDMARKER}


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
    source = raw.decode('utf-8')
    tree = StripDocstrings().visit(ast.parse(source))
    normal = (ast.unparse(tree) + '\n').encode('utf-8')
    tokens = sum(t.type not in IGNORED for t in
                 tokenize.generate_tokens(io.StringIO(normal.decode()).readline))
    return {
        'raw_bytes': len(raw),
        'normalized_bytes': len(normal),
        'normalized_tokens': tokens,
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'gzip9_raw_bytes': len(gzip.compress(raw, compresslevel=9, mtime=0)),
        'gzip9_normalized_bytes': len(gzip.compress(normal, compresslevel=9, mtime=0)),
        'sha256': hashlib.sha256(raw).hexdigest(),
        'imports': [ast.unparse(n) for n in ast.walk(tree)
                    if isinstance(n, (ast.Import, ast.ImportFrom))],
        'public_candidate': ('ACCEPT' in source and 'REJECT' in source
                             and ('load(' in source or 'loads(' in source)),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--manifest', type=Path, default=Path('pinned_sources.json'))
    parser.add_argument('--baselines', type=Path, default=Path('baselines'))
    parser.add_argument('--output', type=Path, default=Path('audit'))
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    rows, archives, seen = [], [], set()

    def visit(raw, provenance):
        digest = hashlib.sha256(raw).hexdigest()
        if digest in seen:
            return
        seen.add(digest)
        with zipfile.ZipFile(io.BytesIO(raw)) as archive:
            for name in archive.namelist():
                if name.endswith('.py'):
                    try:
                        row = metrics(archive.read(name))
                        rows.append({'path': provenance + '::' + name, **row})
                    except (SyntaxError, UnicodeError, tokenize.TokenError):
                        pass
                elif name.endswith('.zip'):
                    visit(archive.read(name), provenance + '::' + name)

    for entry in manifest['files']:
        if entry['type'] != 'file' or not entry['name'].endswith('.zip'):
            continue
        raw = (args.baselines / entry['name']).read_bytes()
        git_blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        if git_blob != entry['sha']:
            raise ValueError('Git blob mismatch: ' + entry['name'])
        archives.append({'name': entry['name'], 'git_blob_sha1': git_blob,
                         'sha256': hashlib.sha256(raw).hexdigest(), 'bytes': len(raw)})
        visit(raw, entry['name'])
    candidates = [row for row in rows if row['public_candidate']]
    keys = ('normalized_tokens', 'ast_nodes', 'normalized_bytes')
    minima = {key: min(row[key] for row in candidates) for key in keys}
    summary = {
        'repository_commit': manifest['head'],
        'python': platform.python_version(),
        'python_implementation': platform.python_implementation(),
        'gzip': 'gzip.compress(data, compresslevel=9, mtime=0); raw and normalized source separately',
        'normalization': 'Remove genuine docstrings; ast.unparse(tree) plus newline; include whole module.',
        'public_candidate_screen': 'Static ACCEPT/REJECT and JSON load detection, followed by manual review of every minimum attainer.',
        'scope': 'Top-level pinned archives and unique recursively embedded archives. Byte-identical archive copies are deduplicated.',
        'archive_count': len(archives), 'unique_archives_including_embedded': len(seen),
        'python_sources': len(rows), 'public_candidates': len(candidates),
        'coordinate_minima': minima,
        'minimum_attainers': {key: [r for r in candidates if r[key] == minima[key]] for key in keys},
        'archives': archives,
    }
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'recursive_python_metrics.json').write_text(json.dumps(rows, indent=2) + '\n')
    (args.output / 'baseline_summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    fields = ('path', 'normalized_tokens', 'ast_nodes', 'normalized_bytes',
              'raw_bytes', 'gzip9_raw_bytes', 'gzip9_normalized_bytes', 'sha256')
    with (args.output / 'baseline_metrics.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fields, extrasaction='ignore')
        writer.writeheader()
        writer.writerows(candidates)
    print(json.dumps({k: v for k, v in summary.items()
                      if k not in ('minimum_attainers', 'archives')}, indent=2))


if __name__ == '__main__':
    main()
