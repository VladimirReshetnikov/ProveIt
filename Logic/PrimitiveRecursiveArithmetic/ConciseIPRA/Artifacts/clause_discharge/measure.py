"""Reproduce source measurements; no minification or hidden helper is excluded."""
from pathlib import Path
import ast
import gzip
import hashlib
import io
import json
import platform
import tokenize

ROOT = Path(__file__).resolve().parent


def measure(path):
    raw = path.read_bytes()
    tree = ast.parse(raw.decode())
    if (tree.body and isinstance(tree.body[0], ast.Expr)
            and isinstance(tree.body[0].value, ast.Constant)
            and type(tree.body[0].value.value) is str):
        tree.body.pop(0)
    normalized = (ast.unparse(tree) + '\n').encode()
    excluded = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
                tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    tokens = sum(t.type not in excluded for t in tokenize.generate_tokens(
        io.StringIO(normalized.decode()).readline))
    return {'path': path.relative_to(ROOT).as_posix(),
            'raw_bytes': len(raw), 'normalized_bytes': len(normalized),
            'significant_tokens': tokens,
            'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'normalized_gzip9': len(gzip.compress(normalized, 9, mtime=0)),
            'raw_gzip9': len(gzip.compress(raw, 9, mtime=0)),
            'sha256': hashlib.sha256(raw).hexdigest()}, normalized


def main():
    paths = [
        'code/checker_deterministic.py',
        'code/checker_explicit.py',
        'reference/prior_name_checker.py',
        'reference/prior_uniform_binding_checker.py',
        'reference/compact_516.py',
        'reference/validated_788.py',
    ]
    # Bounded variants, when present, are additional reported interfaces.
    paths += [p.relative_to(ROOT).as_posix() for p in sorted((ROOT / 'code').glob('*fuel*.py'))
              if not p.stem.endswith('_normalized')]
    rows = []
    normalized_dir = ROOT / 'evidence/normalized'
    normalized_dir.mkdir(exist_ok=True)
    for rel in paths:
        row, normalized = measure(ROOT / rel)
        rows.append(row)
        name = rel.replace('/', '__')
        (normalized_dir / name).write_bytes(normalized)
        (normalized_dir / (name + '.gz')).write_bytes(gzip.compress(normalized, 9, mtime=0))
    chosen, control = rows[:2]
    result = {
        'python': platform.python_version(),
        'normalization': 'remove only module docstring; ast.unparse; one final LF',
        'gzip': 'compression level 9, mtime 0; informative, not minimized',
        'measurements': rows,
        'matched_deterministic_minus_explicit': {
            k: chosen[k] - control[k]
            for k in ['normalized_bytes', 'significant_tokens', 'ast_nodes', 'normalized_gzip9']
        },
        'comparison_limits': [
            'The shared new interface is applied identically to both new checkers.',
            'The deterministic mathematical rule itself has a small source cost.',
            'The whole deterministic checker improves the inspected explicit-rule source envelope.',
            'The separate 516-byte compact and 788-byte validated encodings remain smaller.',
            'No absolute minimality or below-all-corpus claim is made.'
        ]
    }
    (ROOT / 'evidence/metrics.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
