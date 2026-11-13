"""Reproduce a source-size census of a frozen ConciseIPRA checkout.

This script measures source without importing or executing any scanned program.
It reads ZIP member bytes directly, never extracting archive paths.
The syntactic driver heuristic is a shortlist, not a correctness audit.
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


class RemoveDocstrings(ast.NodeTransformer):
    def strip(self, node):
        self.generic_visit(node)
        if (node.body and isinstance(node.body[0], ast.Expr)
                and isinstance(node.body[0].value, ast.Constant)
                and isinstance(node.body[0].value.value, str)):
            node.body.pop(0)
            if not node.body and not isinstance(node, ast.Module):
                node.body.append(ast.Pass())
        return node
    visit_Module = strip
    visit_ClassDef = strip
    visit_FunctionDef = strip
    visit_AsyncFunctionDef = strip


SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def measure(raw):
    tree = RemoveDocstrings().visit(ast.parse(raw))
    source = (ast.unparse(tree) + '\n').encode()
    text = source.decode()
    has_accept = any(isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
                     and n.func.id == 'print' and any(isinstance(a, ast.Constant)
                         and a.value == 'ACCEPT' for a in n.args) for n in ast.walk(tree))
    has_json_input = any(isinstance(n, ast.Call) and
                        ((isinstance(n.func, ast.Name) and n.func.id in ('load','loads','input'))
                         or (isinstance(n.func, ast.Attribute) and n.func.attr in ('load','loads')))
                        for n in ast.walk(tree))
    return {
        'raw_bytes': len(raw),
        'normalized_bytes': len(source),
        'significant_tokens': sum(t.type not in SKIP for t in
            tokenize.generate_tokens(io.StringIO(text).readline)),
        'ast_nodes': len(list(ast.walk(ast.parse(text)))),
        'gzip9_bytes': len(gzip.compress(source, compresslevel=9, mtime=0)),
        'sha256': hashlib.sha256(raw).hexdigest(),
        'normalized_sha256': hashlib.sha256(source).hexdigest(),
        'driver_heuristic': has_accept and has_json_input,
        'packed_execution': any(isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
                                and n.func.id in ('exec','eval','compile') for n in ast.walk(tree)),
    }


def members(raw, prefix, depth=0):
    if depth > 8:
        raise ValueError('Archive nesting exceeds eight levels: ' + prefix)
    with zipfile.ZipFile(io.BytesIO(raw)) as archive:
        for info in archive.infolist():
            if info.is_dir():
                continue
            if info.file_size > 100_000_000:
                raise ValueError('Oversized member: ' + prefix + '!' + info.filename)
            if info.filename.endswith('.py'):
                yield prefix + '!' + info.filename, archive.read(info)
            elif info.filename.endswith('.py.gz'):
                yield prefix + '!' + info.filename, gzip.decompress(archive.read(info))
            elif info.filename.endswith('.zip'):
                yield from members(archive.read(info), prefix + '!' + info.filename, depth+1)


def sources(root):
    for file in sorted((root/'Artifacts').rglob('*.py')):
        yield str(file.relative_to(root)), file.read_bytes()
    for file in sorted((root/'Artifacts').rglob('*.py.gz')):
        yield str(file.relative_to(root)), gzip.decompress(file.read_bytes())
    for file in sorted((root/'Artifacts').rglob('*.zip')):
        yield from members(file.read_bytes(), str(file.relative_to(root)))
    for file in sorted((root/'docs/incoming').glob('*.zip')):
        yield from members(file.read_bytes(), str(file.relative_to(root)))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('root', type=Path)
    parser.add_argument('--output', type=Path, default=Path('census.json'))
    args = parser.parse_args()
    records, errors, cache = [], [], {}
    for path, raw in sources(args.root):
        try:
            sha = hashlib.sha256(raw).hexdigest()
            if sha not in cache:
                cache[sha] = measure(raw)
            records.append(dict(path=path, **cache[sha]))
        except Exception as error:
            errors.append(dict(path=path, error=type(error).__name__ + ': ' + str(error)))
    metrics = ['significant_tokens', 'ast_nodes', 'normalized_bytes', 'gzip9_bytes']
    drivers = [r for r in records if r['driver_heuristic']]
    result = {
        'python': platform.python_version(),
        'commit': 'a0687e8082b7354005d91b0ee105b4fd5ec8cf40',
        'scope': 'All Artifacts Python and recursively nested ZIP Python, plus all docs/incoming ZIP Python; .py.gz sources decompressed',
        'counts': {'measured':len(records), 'parse_errors':len(errors),
                   'unique_sources':len({r['sha256'] for r in records}),
                   'driver_heuristic':len(drivers)},
        'heuristic_minima': {k: min(r[k] for r in drivers) for k in metrics},
        'records': records,
        'parse_errors': errors,
    }
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('records','parse_errors')},indent=2))
    for metric in metrics:
        print('\n' + metric)
        seen = set()
        for r in sorted(drivers,key=lambda r:r[metric]):
            if r['normalized_sha256'] in seen:
                continue
            seen.add(r['normalized_sha256'])
            print(r['significant_tokens'],r['ast_nodes'],r['normalized_bytes'],r['gzip9_bytes'],r['path'])
            if len(seen) >= 12:
                break


if __name__ == '__main__':
    main()
