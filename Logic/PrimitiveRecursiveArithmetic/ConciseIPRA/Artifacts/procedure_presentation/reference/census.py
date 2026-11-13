"""Reproduce a source-size census of the pinned ConciseIPRA snapshot.

Every .py/.py.gz in the tree and directly inside incoming ZIPs is measured.
The census itself does not establish that a measured program is a complete
or sound checker. In particular, controls, rejected experiments, import
wrappers, test programs, and compressed execution wrappers remain labelled.
"""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import sys
import tokenize
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else HERE.parent / 'baseline/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA'
OUTPUT = Path(sys.argv[2]).resolve() if len(sys.argv) > 2 else HERE / 'baseline_source_census.json'
IGNORED = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
           tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}


def main():
    cache, rows, errors, incoming = {}, [], [], []

    def add(path, data):
        try:
            if path.endswith('.gz'):
                data = gzip.decompress(data)
            digest = hashlib.sha256(data).hexdigest()
            if digest not in cache:
                source = data.decode('utf-8')
                tree = ast.parse(source)
                normalized = (ast.unparse(tree) + '\n').encode()
                cache[digest] = {
                    'sha256': digest,
                    'tokens': sum(tok.type not in IGNORED
                                  for tok in tokenize.tokenize(io.BytesIO(normalized).readline)),
                    'ast_nodes': len(list(ast.walk(tree))),
                    'normalized_bytes': len(normalized),
                    'gzip9_bytes': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
                    'raw_bytes': len(data),
                    'accept_literal': any(isinstance(node, ast.Constant)
                                          and node.value == 'ACCEPT' for node in ast.walk(tree)),
                    'direct_eval_exec': any(isinstance(node, ast.Call)
                                            and isinstance(node.func, ast.Name)
                                            and node.func.id in ('eval', 'exec')
                                            for node in ast.walk(tree)),
                }
            rows.append({'path': path, **cache[digest]})
        except Exception as error:
            errors.append({'path': path, 'error': str(error)})

    for path in sorted(ROOT.rglob('*')):
        if path.is_file() and path.name.endswith(('.py', '.py.gz')):
            add(str(path.relative_to(ROOT)), path.read_bytes())
    for archive in sorted((ROOT / 'docs/incoming').glob('*.zip')):
        incoming.append({'path': str(archive.relative_to(ROOT)),
                         'sha256': hashlib.sha256(archive.read_bytes()).hexdigest()})
        with zipfile.ZipFile(archive) as stream:
            for name in sorted(stream.namelist()):
                if name.endswith(('.py', '.py.gz')):
                    add(str(archive.relative_to(ROOT)) + '::' + name, stream.read(name))
    summary = {'commit': 'dd308d5d938b20dce41a1150fa5db49fc53c5d4e',
               'python': sys.version, 'normalization': 'whole-source ast.unparse plus LF; no docstring removal', 'paths': len(rows), 'distinct_sources': len(cache),
               'incoming_archives': incoming, 'parse_errors': errors, 'rows': rows}
    OUTPUT.write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({key: value for key, value in summary.items()
                      if key not in ('rows', 'incoming_archives')}, indent=2))


if __name__ == '__main__':
    main()
