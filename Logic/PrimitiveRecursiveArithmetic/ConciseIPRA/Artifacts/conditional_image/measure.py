"""Measure complete compact modules under the pinned corpus convention."""
import ast
import hashlib
import io
import json
from pathlib import Path
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
PROGRAMS = {
    'reference/control_tokens240.py': (240, 266, 551),
    'reference/control_ast259.py': (252, 259, 595),
    'reference/control_bytes462.py': (267, 298, 462),
    'code/checker_tokens239.py': (239, 261, 553),
    'code/checker_ast257.py': (246, 257, 593),
}
EXCLUDE = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
           tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}

def main():
    rows = []
    for name, expected in PROGRAMS.items():
        raw = (ROOT / name).read_bytes()
        normalized = ast.unparse(ast.parse(raw.decode())) + '\n'
        actual = (sum(t.type not in EXCLUDE for t in tokenize.generate_tokens(io.StringIO(normalized).readline)),
                  sum(1 for _ in ast.walk(ast.parse(normalized))),
                  len(normalized.encode()))
        rows.append({'file': name, 'tokens': actual[0], 'ast_nodes': actual[1],
                     'normalized_bytes': actual[2], 'expected': list(expected),
                     'matches_expected': actual == expected,
                     'raw_sha256': hashlib.sha256(raw).hexdigest(),
                     'normalized_sha256': hashlib.sha256(normalized.encode()).hexdigest()})
    receipt = {'python': sys.version, 'rows': rows,
               'inherited_coordinate_envelope': [240, 259, 462],
               'new_coordinate_envelope_including_inherited_byte_record': [239, 257, 462],
               'one_new_program_beats_all_three_records': False}
    (ROOT / 'evidence/metrics.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))
    if not all(row['matches_expected'] for row in rows):
        raise SystemExit('A size differs from CPython 3.12.14; inspect evidence/metrics.json.')

if __name__ == '__main__':
    main()
