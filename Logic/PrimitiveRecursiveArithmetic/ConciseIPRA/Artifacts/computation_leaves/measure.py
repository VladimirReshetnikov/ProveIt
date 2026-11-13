"""Reproduce whole-module metrics under the repository's normalization contract."""
import ast
import hashlib
import io
import json
from pathlib import Path
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT,
        tokenize.DEDENT, tokenize.ENDMARKER, tokenize.COMMENT}


def measure(path):
    source = path.read_bytes()
    normalized = ast.unparse(ast.parse(source)) + '\n'
    return {
        'file': path.relative_to(ROOT).as_posix(),
        'source_sha256': hashlib.sha256(source).hexdigest(),
        'normalized_sha256': hashlib.sha256(normalized.encode()).hexdigest(),
        'significant_tokens': sum(t.type not in SKIP for t in
            tokenize.generate_tokens(io.StringIO(normalized).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(ast.parse(normalized))),
        'normalized_utf8_bytes': len(normalized.encode()),
    }


def main():
    pairs = [('tokens244.py', 'checker_tokens.py'),
             ('ast265.py', 'checker_ast.py'),
             ('bytes477.py', 'checker_bytes.py')]
    rows = []
    for control, candidate in pairs:
        rows.extend([measure(ROOT / 'controls' / control),
                     measure(ROOT / 'code' / candidate)])
    keys = ('significant_tokens', 'ast_nodes', 'normalized_utf8_bytes')
    old = {k: min(x[k] for x in rows[0::2]) for k in keys}
    new = {k: min(x[k] for x in rows[1::2]) for k in keys}
    if sys.version_info[:2] == (3, 12):
        expected = [(244,272,608),(243,271,616),(249,265,605),
                    (248,264,613),(272,306,477),(270,308,474)]
        for row, values in zip(rows, expected):
            if tuple(row[k] for k in keys) != values:
                raise ValueError(('Unexpected complete-checker metrics', row))
    companions = [measure(ROOT / 'code' / n) for n in
                  ('checker_native.py', 'checker_strict.py')
                  if (ROOT / 'code' / n).is_file()]
    report = {'python_version': sys.version.split()[0],
              'reference_runtime': 'CPython 3.12.14',
              'normalization': "ast.unparse(ast.parse(source)) + '\\n'",
              'modules': rows,
              'incumbent_compact_coordinate_minima': old,
              'proposed_compact_coordinate_minima': new,
              'all_coordinate_minima_strictly_improved': all(new[k] < old[k] for k in keys),
              'one_program_attains_all_minima': False,
              'input_contract': 'Finite exact-integer/list trees; canonical closed guarded public goal.',
              'validated_companions_different_contract': companions,
              'proved_global_optimality': False}
    dest = ROOT / 'evidence' / 'metrics.json'
    dest.write_text(json.dumps(report, sort_keys=True, indent=2) + '\n')
    print(json.dumps({'incumbent': old, 'proposed': new,
                      'validated_companions': companions}, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
