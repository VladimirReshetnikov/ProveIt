"""Reproduce full-module metrics; historical sources are parsed, never run."""
from pathlib import Path
import ast
import gzip
import hashlib
import io
import json
import sys
import tokenize
import zlib

ROOT = Path(__file__).resolve().parent


class StripDocstrings(ast.NodeTransformer):
    def strip(self, node):
        self.generic_visit(node)
        if (node.body and isinstance(node.body[0], ast.Expr)
                and isinstance(node.body[0].value, ast.Constant)
                and isinstance(node.body[0].value.value, str)):
            node.body.pop(0)
        return node
    visit_Module = visit_FunctionDef = visit_AsyncFunctionDef = visit_ClassDef = strip


def measure(data):
    tree = StripDocstrings().visit(ast.parse(data))
    normalized = (ast.unparse(tree) + '\n').encode()
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
               tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    return {
        'sha256': hashlib.sha256(data).hexdigest(),
        'raw': len(data), 'normalized': len(normalized),
        'tokens': sum(t.type not in ignored for t in
                      tokenize.tokenize(io.BytesIO(normalized).readline)),
        'ast': sum(1 for _ in ast.walk(tree)),
        'gzip9_raw': len(gzip.compress(data, compresslevel=9, mtime=0)),
        'gzip9_normalized': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
    }


def main(write=False):
    paths = sorted((ROOT / 'code').glob('*.py'))
    paths += sorted((ROOT / 'reference').glob('*_frontier.py'))
    measured = {str(p.relative_to(ROOT)): measure(p.read_bytes()) for p in paths}
    census = json.loads((ROOT / 'evidence/corpus.json').read_text())
    mismatches = []
    for old in census['sources']:
        path = ROOT / 'reference/source_corpus' / (old['sha256'] + '.py')
        new = measure(path.read_bytes())
        for key, value in new.items():
            if old[key] != value:
                mismatches.append({'source': old['sha256'], 'field': key,
                                   'expected': old[key], 'actual': value})
    result = {'python': sys.version, 'zlib': zlib.ZLIB_VERSION,
              'programs': measured, 'frozen_sources': len(census['sources']),
              'corpus_metric_mismatches': mismatches}
    if write:
        (ROOT / 'evidence/measurements.json').write_text(json.dumps(result, indent=2) + '\n')
        for path in paths:
            path.with_suffix('.py.gz').write_bytes(
                gzip.compress(path.read_bytes(), compresslevel=9, mtime=0))
    return result


if __name__ == '__main__':
    result = main('--write' in sys.argv)
    print(json.dumps(result, indent=2))
    if result['corpus_metric_mismatches']:
        raise SystemExit('Runtime-sensitive corpus metric mismatch; inspect the report.')
