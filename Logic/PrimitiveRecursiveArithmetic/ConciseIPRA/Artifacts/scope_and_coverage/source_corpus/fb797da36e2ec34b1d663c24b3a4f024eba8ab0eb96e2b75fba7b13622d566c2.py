"""Measure the complete delivered checkers and exact pinned comparators."""
from pathlib import Path
import json
import platform
from source_measure import metrics

ROOT = Path(__file__).resolve().parent.parent
PROGRAMS = [
    ('Old token minimum', 'comparison/old_token_min.py'),
    ('Old AST minimum', 'comparison/old_ast_min.py'),
    ('Old byte minimum', 'comparison/old_byte_min.py'),
    ('New Choice byte program', 'code/choice_checker.py'),
    ('New Choice token profile', 'code/choice_tokens.py'),
    ('New Choice AST profile', 'code/choice_structure.py'),
    ('New scalar-feedback theory', 'code/scalar_sc_checker.py'),
]


def main():
    rows = []
    for label, path in PROGRAMS:
        measured = metrics(ROOT / path)
        measured.pop('core', None)
        rows.append({'label': label, 'path': path, **measured})
    keys = ['normalized_tokens', 'ast_nodes', 'normalized_bytes']
    result = {
        'python': platform.python_version(),
        'implementation': platform.python_implementation(),
        'metric': 'Entire module; genuine docstrings/comments removed; ast.unparse plus final newline',
        'old_coordinate_envelope': {k: min(row[k] for row in rows[:3]) for k in keys},
        'new_choice_coordinate_envelope': {k: min(row[k] for row in rows[3:6]) for k in keys},
        'programs': rows,
        'byte_saving': rows[2]['normalized_bytes'] - rows[3]['normalized_bytes'],
        'percent_byte_saving': 100 * (rows[2]['normalized_bytes'] - rows[3]['normalized_bytes']) / rows[2]['normalized_bytes'],
    }
    (ROOT / 'evidence/measurements.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
