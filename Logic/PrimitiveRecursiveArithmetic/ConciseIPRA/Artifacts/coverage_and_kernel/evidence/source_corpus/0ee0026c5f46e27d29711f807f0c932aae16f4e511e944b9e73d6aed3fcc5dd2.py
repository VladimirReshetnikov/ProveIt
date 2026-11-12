"""Read-only reproduction of package identities, measurements, and finite checks.

Run from any directory: python3 reproduce.py
During authoring only: python3 reproduce.py --skip-manifest

MANIFEST.json must contain {"files": [{"path": "relative/posix/path",
"bytes": 123, "sha256": "64 lowercase hexadecimal digits"}, ...]}.
Additional top-level metadata is allowed. The manifest omits itself and lists
every other regular payload file. No delivered file is written by this driver.
Exact AST/unparser measurements can depend on the running CPython version.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import platform
import re
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
os.environ['PYTHONDONTWRITEBYTECODE'] = '1'
ROOT = Path(__file__).resolve().parent
MEASURES = ('source_tokens', 'normalized_tokens', 'ast_nodes',
            'normalized_bytes', 'raw_bytes', 'sha256')
COORDINATES = ('normalized_tokens', 'ast_nodes', 'normalized_bytes')


def read_json(path):
    return json.loads(path.read_text(encoding='utf-8'))


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def equal(actual, expected, label):
    if actual != expected:
        raise ValueError(label + ' differs from its recorded receipt: '
                         + repr(actual)[:300] + ' != ' + repr(expected)[:300])


def payload_path(name):
    if not isinstance(name, str):
        raise ValueError('Manifest path must be a string')
    relative = PurePosixPath(name)
    if relative.is_absolute() or not relative.parts or '..' in relative.parts:
        raise ValueError('Invalid relative payload path: ' + repr(name))
    path = ROOT.joinpath(*relative.parts)
    if not path.resolve().is_relative_to(ROOT):
        raise ValueError('Payload path escapes the package: ' + name)
    return path


def verify_manifest(skip):
    if skip:
        return {'status': 'SKIPPED', 'reason': '--skip-manifest authoring option'}
    path = ROOT / 'MANIFEST.json'
    if not path.is_file():
        raise ValueError('MANIFEST.json is missing; --skip-manifest is only for authoring')
    document = read_json(path)
    rows = document.get('files')
    if not isinstance(rows, list):
        raise ValueError('MANIFEST.json must have a files array')
    names, byte_count = set(), 0
    for row in rows:
        name = row['path']
        if name in names or name == 'MANIFEST.json':
            raise ValueError('Duplicate or self-referential manifest entry: ' + name)
        item = payload_path(name)
        size, digest = row['bytes'], row['sha256']
        if type(size) is not int or size < 0:
            raise ValueError('Invalid manifest byte length: ' + name)
        if not isinstance(digest, str) or not re.fullmatch('[0-9a-f]{64}', digest):
            raise ValueError('Invalid manifest SHA-256: ' + name)
        if not item.is_file():
            raise ValueError('Missing payload: ' + name)
        data = item.read_bytes()
        equal(len(data), size, 'Payload byte length ' + name)
        equal(hashlib.sha256(data).hexdigest(), digest, 'Payload SHA-256 ' + name)
        names.add(name)
        byte_count += size
    actual = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*')
              if p.is_file() and p != path}
    equal(sorted(actual), sorted(names), 'Complete payload inventory')
    return {'status': 'PASS', 'files': len(names), 'bytes': byte_count}


def run_json(script, *arguments):
    command = [sys.executable, '-B', str(ROOT / script), *map(str, arguments)]
    result = subprocess.run(command, cwd=ROOT, env=os.environ.copy(), text=True,
                            capture_output=True, timeout=180)
    if result.returncode:
        raise RuntimeError(script + ' failed (exit ' + str(result.returncode) + '): '
                           + (result.stderr or result.stdout)[-1800:])
    try:
        return json.loads(result.stdout)
    except json.JSONDecodeError as exc:
        raise ValueError(script + ' did not emit one JSON result') from exc


def compare_measurements(actual, expected, label, recorded_python):
    for field in MEASURES:
        try:
            equal(actual[field], expected[field], label + ': ' + field)
        except ValueError as exc:
            raise ValueError(str(exc) + '. Receipt runtime: CPython '
                             + recorded_python + '; running: '
                             + platform.python_implementation() + ' '
                             + platform.python_version()
                             + '. AST/unparser metrics can change between versions.') from exc


def verify_corpus():
    recorded = read_json(ROOT / 'evidence/corpus_sources.json')
    with tempfile.TemporaryDirectory(prefix='ipra-reproduction-census-') as directory:
        run_json('reference/audit_corpus.py', '--output', directory)
        current = read_json(Path(directory) / 'full_inventory.json')
    for field in ('commit', 'measurer_sha256', 'direct_archives',
                  'archive_occurrences_including_embedded', 'python_occurrences',
                  'distinct_python_sources', 'parse_failures', 'archives'):
        equal(current[field], recorded[field], 'Corpus ' + field)
    equal(current['parse_failures'], [], 'Corpus parse failures')
    old_rows = {row['path']: row for row in recorded['sources']}
    rows = {row['path']: row for row in current['sources']}
    equal(sorted(rows), sorted(old_rows), 'Archived Python occurrence inventory')
    for name, row in rows.items():
        compare_measurements(row, old_rows[name], name, recorded['python'])

    classification = read_json(ROOT / 'evidence/corpus_classification.json')
    equal(classification['commit'], current['commit'], 'Classification commit')
    envelope = dict(zip(COORDINATES, (classification['whole_program_envelope'][k]
                                    for k in ('tokens', 'ast', 'bytes'))))
    unique = {row['sha256']: row for row in rows.values()}
    relevant = {digest for digest, row in unique.items()
                if any(row[key] <= envelope[key] for key in COORDINATES)}
    classified = {row['sha256']: row for row in classification['sources']}
    equal(set(classified), relevant, 'Frontier classification coverage')
    equal(len(classified), classification['classification_count'],
          'Frontier classification count')
    for digest, row in classified.items():
        for short, long in zip(('tokens', 'ast', 'bytes'), COORDINATES):
            equal(row[short], unique[digest][long], 'Classified source ' + digest)
    complete = [unique[digest] for digest, row in classified.items()
                if row['complete_checker']]
    recomputed = {key: min(row[key] for row in complete) for key in COORDINATES}
    equal(recomputed, envelope, 'Classified complete-program envelope')
    return current, classification, envelope


def verify_checker_metrics(corpus_envelope):
    recorded = read_json(ROOT / 'evidence/checker_metrics.json')
    spec = importlib.util.spec_from_file_location(
        'reproduction_source_measure', ROOT / 'reference/source_measure.py')
    measure = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(measure)
    rows = {}
    for row in recorded['programs']:
        path = payload_path(row['file'])
        actual = measure.metrics(path)
        compare_measurements(actual, row, row['file'], recorded['python'])
        rows[row['file']] = actual
    selected = [rows['code/' + name] for name in
                ('checker.py', 'checker_bytes.py', 'checker_ast.py')]
    envelope = {key: min(row[key] for row in selected) for key in COORDINATES}
    equal(recorded['current_corpus_envelope'], corpus_envelope,
          'Recorded current corpus envelope')
    equal(envelope, recorded['new_scalar_R_family_envelope'], 'New family envelope')
    improvements = {key: envelope[key] < corpus_envelope[key] for key in COORDINATES}
    equal(improvements, recorded['strict_coordinate_improvements'],
          'Strict coordinate improvement flags')
    dominance = any(all(row[key] < corpus_envelope[key] for key in COORDINATES)
                    for row in selected)
    equal(dominance, recorded['one_new_program_below_all_current_coordinates'],
          'Single-program dominance flag')
    return {'complete_program_rows': len(rows), 'family_envelope': envelope,
            'one_program_below_all_old_coordinates': dominance,
            'recorded_python': recorded['python'],
            'runtime_matches_recording': platform.python_implementation() == 'CPython'
            and platform.python_version() == recorded['python']}


def verify_proofs():
    produced = run_json('tests/producer.py', '--check')
    equal(produced['status'], 'PASS', 'Producer regeneration')
    checked = run_json('tests/run_checker_tests.py')
    recorded = read_json(ROOT / 'evidence/checker_validation.json')
    for field in ('status', 'proof_packets', 'positive', 'negative',
                  'complete_program_runs', 'mutation_runs', 'programs',
                  'mutations', 'failures'):
        equal(checked[field], recorded[field], 'Proof checking ' + field)
    equal(checked['status'], 'PASS', 'Proof checking verdict')
    equal(checked['failures'], [], 'Proof checking failures')
    equal(produced['regenerated_packets'], checked['proof_packets'],
          'Regenerated packet count')
    cases = read_json(ROOT / 'tests/cases.json')['cases']
    equal(sorted(p.stem for p in (ROOT / 'tests/fixtures').glob('*.json')),
          sorted(case['name'] for case in cases), 'Exact fixture inventory')
    return {'regenerated_packets': produced['regenerated_packets'],
            'positive': checked['positive'], 'negative': checked['negative'],
            'programs': len(checked['programs']),
            'ordinary_and_optimized_runs': checked['complete_program_runs'],
            'mutation_controls': checked['mutation_runs']}


def verify_arithmetic():
    recorded = read_json(ROOT / 'evidence/arithmetic_validation.json')
    for name, digest in recorded['source_sha256'].items():
        equal(sha256(payload_path(name)), digest, 'Arithmetic source ' + name)
    actual = run_json('tests/check_arithmetic.py')
    for field in ('status', 'arithmetic_shortcuts', 'checks', 'total_checks', 'cache_entries'):
        equal(actual[field], recorded[field], 'Arithmetic ' + field)
    equal(actual['status'], 'PASS', 'Arithmetic verdict')
    equal(actual['arithmetic_shortcuts'], False, 'Arithmetic shortcut policy')
    return {'total': actual['total_checks'], 'groups': len(actual['checks']),
            'arithmetic_shortcuts': actual['arithmetic_shortcuts']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-manifest', action='store_true',
                        help='Authoring only: explicitly skip final package identity checks')
    args = parser.parse_args()
    manifest = verify_manifest(args.skip_manifest)
    corpus, classification, envelope = verify_corpus()
    metrics = verify_checker_metrics(envelope)
    proofs = verify_proofs()
    arithmetic = verify_arithmetic()
    return {
        'status': 'PASS', 'python': platform.python_version(),
        'implementation': platform.python_implementation(),
        'manifest': manifest,
        'corpus': {
            'commit': corpus['commit'], 'direct_archives': corpus['direct_archives'],
            'embedded_archives': corpus['archive_occurrences_including_embedded']
            - corpus['direct_archives'], 'python_occurrences': corpus['python_occurrences'],
            'distinct_python_sources': corpus['distinct_python_sources'],
            'frontier_classifications': classification['classification_count'],
        },
        'source_metrics': metrics, 'proof_checks': proofs,
        'arithmetic_checks': arithmetic,
        'scope': 'Read-only archive, source, receipt, and finite executable reproduction; '
                 'not a proof-assistant verification of the universal metatheorems.',
    }


if __name__ == '__main__':
    try:
        result = main()
    except Exception as error:
        print(json.dumps({'status': 'FAIL', 'python': platform.python_version(),
                          'error': str(error)}, indent=2))
        raise SystemExit(1)
    print(json.dumps(result, indent=2))
