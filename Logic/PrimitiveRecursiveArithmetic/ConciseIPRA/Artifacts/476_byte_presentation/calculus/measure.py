"""Measure complete literal standalone profiles, including parsing and output.

Readable counterparts carry explanatory module docstrings. Profile generation
removes that non-executable documentation; measurement itself removes nothing.
The generated profile is independently runnable and imports no helper here.
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


def make_profile(path):
    tree = ast.parse(path.read_bytes())
    if tree.body and isinstance(tree.body[0], ast.Expr) and isinstance(tree.body[0].value, ast.Constant) and isinstance(tree.body[0].value.value, str):
        tree.body.pop(0)
    output = ROOT / (path.stem + '_normalized.py')
    output.write_text(ast.unparse(tree) + '\n')
    return output


def measure(path):
    raw = path.read_bytes()
    tree = ast.parse(raw)
    normalized = (ast.unparse(tree) + '\n').encode()
    excluded = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.INDENT,
                tokenize.DEDENT, tokenize.NEWLINE, tokenize.NL, tokenize.COMMENT}
    tokens = [t for t in tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)
              if t.type not in excluded]
    return {'tokens': len(tokens), 'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'normalized_bytes': len(normalized),
            'gzip9': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
            'source_sha256': hashlib.sha256(raw).hexdigest(),
            'normalized_sha256': hashlib.sha256(normalized).hexdigest()}


def main():
    result = {'python': sys.version.split()[0],
              'metric': 'Whole literal standalone *_normalized.py profile; ast.unparse plus one LF; no exclusions',
              'profile_generation': 'Readable counterparts differ only by their leading explanatory docstring and source formatting; profiles import no helper.',
              'checker': measure(make_profile(ROOT / 'checker.py')),
              'control_split': measure(make_profile(ROOT / 'control_split.py')),
              'control_inherited': measure(make_profile(ROOT / 'control_inherited.py'))}
    (ROOT / 'evidence' / 'metrics.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


if __name__ == '__main__':
    print(json.dumps(main(), indent=2))
