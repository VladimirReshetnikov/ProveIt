"""Measure each complete candidate/control module without modifying it.

Run with CPython 3.12.14 to reproduce the frozen corpus convention exactly.
The four compact profiles contain no docstrings; none are stripped here.
The supporting sources retain their explanatory docstrings in this count.
The normalizer is ast.unparse followed by one LF. Source is parsed and
compiled for syntax checking only; no checker or certificate is executed.
"""
from pathlib import Path
import argparse
import ast
import hashlib
import io
import json
import platform
import tokenize

ROOT = Path(__file__).resolve().parent
PROGRAMS = (
    'code/checker479.py',
    'controls/bytes487.py',
    'controls/tokens248.py',
    'controls/ast270.py',
    'code/checker_readable.py',
    'code/checker_strict.py',
    'controls/strict_guarded_original.py',
)
SKIP = {
    tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
    tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT,
}


def measure(relative):
    raw = (ROOT / relative).read_bytes()
    normalized = ast.unparse(ast.parse(raw)) + '\n'
    compile(normalized, relative, 'exec')
    return {
        'path': relative,
        'sha256': hashlib.sha256(raw).hexdigest(),
        'source_bytes': len(raw),
        'significant_tokens': sum(
            token.type not in SKIP for token in
            tokenize.generate_tokens(io.StringIO(normalized).readline)
        ),
        'ast_nodes': sum(1 for _ in ast.walk(ast.parse(normalized))),
        'normalized_bytes': len(normalized.encode('utf-8')),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        help='optionally also write the JSON result here')
    args = parser.parse_args()
    result = {
        'python': platform.python_version(),
        'normalization': 'ast.unparse plus one LF; no docstrings removed',
        'measurements': [measure(path) for path in PROGRAMS],
        'comparison_limits': [
            'The compact checker assumes the documented canonical public-goal contract.',
            'The token, AST, and byte incumbents are different programs.',
            'The token and AST controls consume one physical JSON line.',
            'The candidate and byte control consume ordinary multiline JSON.',
            'No new axiomatization or absolute minimality is claimed.',
        ],
    }
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding='utf-8')
    print(text, end='')


if __name__ == '__main__':
    main()
