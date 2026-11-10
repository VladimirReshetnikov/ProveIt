"""Measure whole standalone programs with the unchanged inherited measurer."""
import importlib.util
import json
from pathlib import Path
import platform

ROOT = Path(__file__).resolve().parent.parent
PROGRAMS = [
    ('Current generated-assumptions I', 'reference/old_checker.py'),
    ('Current AST leader', 'reference/old_checker_ast.py'),
    ('I with matched JSON import', 'reference/old_import_matched.py'),
    ('Direct scalar R, old source protocol', 'reference/scalar_successor_direct.py'),
    ('Direct scalar R, matched import', 'reference/scalar_successor_direct_bytes.py'),
    ('Generated-source scalar R', 'code/checker.py'),
    ('Generated-source scalar R, byte profile', 'code/checker_bytes.py'),
    ('Generated-source scalar R, AST profile', 'code/checker_ast.py'),
    ('Readable scalar R', 'code/readable_checker.py'),
    ('Generated-source matched I control', 'reference/old_generated_source_matched.py'),
    ('Generated-source matched I byte control', 'reference/old_generated_source_bytes_matched.py'),
]


def main():
    spec = importlib.util.spec_from_file_location(
        'inherited_source_measure', ROOT / 'reference/source_measure.py'
    )
    measure = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(measure)
    rows = []
    for label, name in PROGRAMS:
        values = measure.metrics(ROOT / name)
        values.pop('core', None)
        rows.append({'label': label, 'file': name, **values})
    keys = ('normalized_tokens', 'ast_nodes', 'normalized_bytes')
    selected = [r for r in rows if r['file'] in (
        'code/checker.py', 'code/checker_bytes.py', 'code/checker_ast.py'
    )]
    envelope = {key: min(row[key] for row in selected) for key in keys}
    old = dict(zip(keys, (281, 315, 685)))
    result = {
        'python': platform.python_version(),
        'metric': 'Complete module, genuine docstrings/comments removed; ast.unparse plus final newline.',
        'current_corpus_envelope': old,
        'new_scalar_R_family_envelope': envelope,
        'strict_coordinate_improvements': {key: envelope[key] < old[key] for key in keys},
        'one_new_program_below_all_current_coordinates': any(
            all(row[key] < old[key] for key in keys) for row in selected
        ),
        'attribution': 'Generated-source arithmetic packets improve the checking interface for I and R. The R base adds two tokens, two AST nodes, and two bytes in matched comparisons. JSON import and driver changes are ordinary implementation choices.',
        'programs': rows,
    }
    (ROOT / 'evidence/checker_metrics.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'programs'}, indent=2))


if __name__ == '__main__':
    main()
