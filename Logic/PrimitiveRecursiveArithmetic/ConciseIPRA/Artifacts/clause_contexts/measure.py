"""Reproduce complete-checker metrics without importing any checker."""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
PROFILES = [
    ('Pinned five-pattern tagged checker', 'code/horn/reference/control.py'),
    ('Five-pattern arity and scope control', 'code/ranked/control_five_recursive_arity.py'),
    ('Four-pattern explicit tree checker', 'code/ranked/checker_recursive_arity.py'),
    ('Four-pattern ranked tree checker', 'code/ranked/checker_ranked_scoped.py'),
    ('Four-pattern empty-antecedent packets', 'code/packet/checker_empty_antecedent.py'),
    ('Selected four-pattern packet checker', 'code/packet/checker.py'),
]


def normalized(path):
    tree = ast.parse(path.read_text())
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if (node.body and isinstance(node.body[0], ast.Expr)
                    and isinstance(node.body[0].value, ast.Constant)
                    and isinstance(node.body[0].value.value, str)):
                node.body.pop(0)
    return (ast.unparse(tree) + '\n').encode(), tree


def measure(label, relative):
    path = ROOT / relative
    data, tree = normalized(path)
    excluded = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
                tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}
    tokens = sum(token.type not in excluded for token in
                 tokenize.generate_tokens(io.StringIO(data.decode()).readline))
    destination = ROOT / 'evidence' / 'normalized' / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(data)
    destination.with_suffix('.py.gz').write_bytes(gzip.compress(data, compresslevel=9, mtime=0))
    return {'label': label, 'path': relative,
            'normalized_bytes': len(data), 'significant_tokens': tokens,
            'ast_nodes': len(list(ast.walk(tree))),
            'gzip9_bytes': len(gzip.compress(data, compresslevel=9, mtime=0)),
            'source_bytes': path.stat().st_size,
            'source_gzip9_bytes': len(gzip.compress(path.read_bytes(), compresslevel=9, mtime=0)),
            'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
            'normalized_sha256': hashlib.sha256(data).hexdigest()}


def main():
    report = {'python': sys.version, 'platform': platform.platform(),
              'normalization': 'Remove documentation strings; ast.unparse; one final LF.',
              'gzip': 'Level 9, mtime=0, applied to both normalized and full source bytes.',
              'profiles': [measure(label, path) for label, path in PROFILES],
              'unselected_experiments': [measure(
                  'Support-derived rank (exploratory, not in the verified checker suite)',
                  'experiments/checker_support_experiment.py')]}
    (ROOT / 'evidence' / 'metrics.json').write_text(json.dumps(report, indent=2) + '\n')
    for p in report['profiles']:
        print(f"{p['normalized_bytes']:4} bytes  {p['significant_tokens']:3} tokens  "
              f"{p['ast_nodes']:3} AST  {p['gzip9_bytes']:4} gzip9  {p['label']}")


if __name__ == '__main__':
    main()
