"""Inventory and measure every Python source in a pinned recursive ZIP corpus.

No supplied Python source is executed. Completeness classification is a
separate, reviewed boundary artifact: tiny build/test helpers are not kernels.
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
import zipfile
import zlib

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


def measure(raw):
    source = raw.decode('utf-8')
    tree = ast.parse(source)
    docs = set()
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef,
                             ast.AsyncFunctionDef, ast.ClassDef)):
            if (node.body and isinstance(node.body[0], ast.Expr)
                    and isinstance(node.body[0].value, ast.Constant)
                    and isinstance(node.body[0].value.value, str)):
                value = node.body[0].value
                docs.add(((value.lineno, value.col_offset),
                          (value.end_lineno, value.end_col_offset)))
    source_tokens = sum(
        t.type not in IGNORED and (t.start, t.end) not in docs
        for t in tokenize.generate_tokens(io.StringIO(source).readline))
    tree = ast.fix_missing_locations(StripDocstrings().visit(tree))
    normalized = (ast.unparse(tree) + '\n').encode('utf-8')
    normalized_tokens = sum(
        t.type not in IGNORED for t in tokenize.generate_tokens(
            io.StringIO(normalized.decode('utf-8')).readline))
    return {
        'source_tokens': source_tokens,
        'normalized_tokens': normalized_tokens,
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'normalized_bytes': len(normalized),
        'raw_bytes': len(raw),
        'gzip9_raw': len(gzip.compress(raw, compresslevel=9, mtime=0)),
        'gzip9_normalized': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
        'sha256': hashlib.sha256(raw).hexdigest(),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('archives', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    source_dir = args.output / 'sources'
    source_dir.mkdir(exist_ok=True)
    sources = {}
    archives = []

    def ingest(raw, origin):
        digest = hashlib.sha256(raw).hexdigest()
        if digest in sources:
            sources[digest]['origins'].append(origin)
            return
        try:
            row = measure(raw)
        except Exception as error:
            row = {'sha256': digest, 'error': str(error)}
        row['origins'] = [origin]
        sources[digest] = row
        (source_dir / (digest + '.py')).write_bytes(raw)

    def scan(raw, origin):
        with zipfile.ZipFile(io.BytesIO(raw)) as archive:
            for info in archive.infolist():
                if info.filename.endswith('.py'):
                    ingest(archive.read(info), origin + '!' + info.filename)
                elif info.filename.endswith('.zip'):
                    scan(archive.read(info), origin + '!' + info.filename)

    for path in sorted(args.archives.glob('*.zip')):
        raw = path.read_bytes()
        archives.append({
            'name': path.name, 'bytes': len(raw),
            'sha256': hashlib.sha256(raw).hexdigest(),
            'git_blob': hashlib.sha1(
                b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()})
        scan(raw, path.name)
    result = {
        'python': platform.python_version(),
        'implementation': platform.python_implementation(),
        'zlib': zlib.ZLIB_RUNTIME_VERSION,
        'archive_count': len(archives),
        'archives': archives,
        'unique_sources': len(sources),
        'occurrences': sum(len(row['origins']) for row in sources.values()),
        'sources': list(sources.values()),
    }
    (args.output / 'corpus_metrics.json').write_text(
        json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: value for key, value in result.items()
                      if key not in ('archives', 'sources')}, indent=2))


if __name__ == '__main__':
    main()
