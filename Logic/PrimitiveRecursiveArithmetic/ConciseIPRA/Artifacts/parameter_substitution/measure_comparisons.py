"""Reproduce the seven incoming-source comparisons without importing them.

Run with CPython 3.12.14 for the frozen ast.unparse measurements. Sources,
hashes, and all measurement inputs are bundled in this archive. Results are
printed as JSON and checked against evidence/incoming_metrics.json.
"""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import sys
import tokenize


ROOT = Path(__file__).resolve().parent


class RemoveDocstrings(ast.NodeTransformer):
    def visit(self, node):
        node = super().visit(node)
        if (isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))
                and node.body and isinstance(node.body[0], ast.Expr)
                and isinstance(node.body[0].value, ast.Constant)
                and isinstance(node.body[0].value.value, str)):
            node.body.pop(0)
        return node


def measure(item):
    raw = (ROOT / item['bundled_path']).read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != item['sha256']:
        raise ValueError('Source hash mismatch: ' + item['bundled_path'])
    tree = RemoveDocstrings().visit(ast.parse(raw.decode('utf-8')))
    normalized = ast.unparse(tree) + '\n'
    encoded = normalized.encode('utf-8')
    excluded = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
                tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    tokens = sum(t.type not in excluded
                 for t in tokenize.generate_tokens(io.StringIO(normalized).readline))
    return {'source': item['original_extracted_path'], 'sha256': digest,
            'normalized_bytes': len(encoded), 'tokens': tokens,
            'ast_nodes': len(list(ast.walk(tree))),
            'gzip9': len(gzip.compress(encoded, compresslevel=9, mtime=0))}


def main():
    provenance = json.loads((ROOT / 'evidence/comparison_provenance.json').read_text())
    expected = json.loads((ROOT / 'evidence/incoming_metrics.json').read_text())
    actual = [measure(item) for item in provenance['comparisons']]
    if actual != expected:
        raise RuntimeError('Comparison measurements differ from the frozen table; '
                           'use CPython 3.12.14 and inspect the bundled source hashes.')
    print(json.dumps(actual, indent=2))
    print('Verified all seven bundled comparisons.', file=sys.stderr)


if __name__ == '__main__':
    main()
