"""Remeasure complete programs with the unchanged corpus normalizer.

This supporting program is not imported by a proof checker. Run from any
directory with Python 3.12; it writes evidence/final_metrics.json and a
compact CSV table. All measured checker imports and verdict drivers count.
"""
from pathlib import Path
import csv
import hashlib
import importlib.util
import json
import platform

ROOT = Path(__file__).resolve().parents[1]
NORMALIZER = ROOT / 'reference/source_measure.py'
SPEC = importlib.util.spec_from_file_location('corpus_source_measure', NORMALIZER)
MEASURE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MEASURE)
COORDINATES = ('normalized_tokens', 'ast_nodes', 'normalized_bytes')


def measured(relative, role):
    result = MEASURE.metrics(ROOT / relative)
    result.pop('core', None)
    return {'file': relative, 'role': role, **result}


def main():
    baseline = [measured('reference/baseline_' + name + '.py', 'frozen baseline')
                for name in ('tokens', 'structure', 'bytes')]
    candidate = [measured('code/kernel_' + name + '.py', 'complete focused checker')
                 for name in ('tokens', 'structure', 'bytes')]
    inherited = json.loads((ROOT / 'evidence/inherited_sources.json').read_text())
    expected = {entry['destination']: entry['sha256'] for entry in inherited}
    for row in baseline:
        if row['sha256'] != expected[row['file']]:
            raise ValueError('Changed frozen baseline: ' + row['file'])
    old_min = {key: min(row[key] for row in baseline) for key in COORDINATES}
    new_min = {key: min(row[key] for row in candidate) for key in COORDINATES}
    for row in candidate:
        row['difference_from_old_coordinate_minima'] = {
            key: row[key] - old_min[key] for key in COORDINATES}
        row['strictly_below_each_old_coordinate'] = {
            key: row[key] < old_min[key] for key in COORDINATES}
        row['single_source_below_all_old_coordinates'] = all(
            row[key] < old_min[key] for key in COORDINATES)
    report = {
        'repository': 'VladimirReshetnikov/ProveIt',
        'commit': '70feebabe24445912ae5eb336a6d7e9ba40a882b',
        'python': platform.python_version(),
        'implementation': platform.python_implementation(),
        'normalizer': 'reference/source_measure.py',
        'normalizer_sha256': hashlib.sha256(NORMALIZER.read_bytes()).hexdigest(),
        'reproduce_command': 'python3 code/measure_complete_sources.py',
        'scope': 'Entire source module, including imports, input call and verdict driver; genuine docstrings removed and ast.unparse applied.',
        'shared_ambient_dependencies': ['Python interpreter and builtin operations', 'standard-library JSON parser'],
        'old_coordinatewise_envelope': old_min,
        'new_separate_profile_envelope': new_min,
        'separate_profile_improvement': {key: new_min[key] < old_min[key] for key in COORDINATES},
        'any_single_profile_below_all_old_coordinates': any(
            row['single_source_below_all_old_coordinates'] for row in candidate),
        'comparison_warning': 'Each envelope combines minima attained by different programs. These are finite-corpus source measurements, not a universal lower bound or an absolute-minimality theorem.',
        'baseline': baseline,
        'focused': candidate,
    }
    destination = ROOT / 'evidence'
    destination.mkdir(exist_ok=True)
    (destination / 'final_metrics.json').write_text(json.dumps(report, indent=2) + '\n')
    with (destination / 'final_metrics.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, ('file', 'role', *COORDINATES, 'raw_bytes', 'sha256'),
                                extrasaction='ignore')
        writer.writeheader()
        writer.writerows(baseline + candidate)
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
