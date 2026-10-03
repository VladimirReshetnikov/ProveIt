#!/usr/bin/env python3
"""Isolated replay driver; only path handling, execution, and result comparison.

The producer/independent scripts implement the original calculations. This driver
neither changes their mathematics nor treats floating-point output as certified.
"""
import argparse
import datetime as dt
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
EXACT_FILES = [
    'producer/exact_values_0_202.json',
    'producer/symbolic_validation.json',
    'independent/exact_h_0_600.txt',
    'extensions/routh_certificates_2_40.json',
    'extensions/independent_complex_root_counts.json',
    'extensions/compound_graph_certificate.json',
    'extensions/certificate.json',
    'extensions/r4_exact_certificate.json',
    'extensions/exact_h_r4_0_100.json',
    'extensions/rational_phase_certificates_30_37.json',
    'extensions/phase_certificate.json',
    'extensions/uniform_threshold_certificate.json',
]
FLOAT_FILES = [
    'producer/numerics_120dps.json',
    'producer/numerics_150dps.json',
    'producer/inverse_validation.json',
    'independent/independent_checks.json',
]
INDEPENDENT_EXACT_KEYS = [
    'lyapunov_derivative_exact', 'jacobian_characteristic',
    'indicial_factorization_exact', 'a11', 'a11_exact', 'a20',
    'stirling_log_gamma_x_plus3_coefficient', 'oeis_first29_exact',
    'producer_first30_exact', 'exact_recurrence_nmax', 'exact_terms_sha256',
    'two_exact_recurrences_agree_through80', 'all_exact_boolean_checks_pass',
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def compare(output, relative):
    reference, generated = ROOT / 'data' / relative, output / relative
    result = {'reference_sha256': sha(reference), 'generated_sha256': sha(generated)}
    result['bytes_equal'] = result['reference_sha256'] == result['generated_sha256']
    if reference.suffix == '.json':
        result['json_equal'] = json.loads(reference.read_text()) == json.loads(generated.read_text())
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output-dir', required=True, type=Path,
                    help='A fresh output directory, normally made by replay.sh')
    args = ap.parse_args()
    out = args.output_dir.resolve()
    if out == ROOT or ROOT in out.parents:
        ap.error('The output directory must be outside the release tree.')
    out.mkdir(parents=True, exist_ok=True)
    if any(out.iterdir()):
        ap.error('The output directory must be empty.')
    for name in ('producer', 'independent', 'extensions', 'logs'):
        (out / name).mkdir()
    environment = {
        'python': sys.version,
        'implementation': platform.python_implementation(),
        'platform': platform.platform(),
        'machine': platform.machine(),
        'packages': {name: importlib.metadata.version(name)
                     for name in ('mpmath', 'sympy', 'numpy', 'scipy')},
    }
    write_json(out / 'environment.json', environment)
    summary = {
        'schema_version': 1,
        'started_utc': dt.datetime.now(dt.timezone.utc).isoformat(),
        'environment': environment,
        'bundled_script_sha256': {str(p.relative_to(ROOT)): sha(p)
                                  for p in sorted((ROOT / 'code').rglob('*.py'))},
        'numerical_status': 'Exploratory, non-interval-certified floating-point evidence only.',
        'stages': [],
    }
    # Checking every shipped data file also proves replay does not overwrite it.
    before = {str(p.relative_to(ROOT)): sha(p)
              for p in sorted((ROOT / 'data').rglob('*')) if p.is_file()}
    stages = [
        ('exact_symbolics', 'verify_symbolics.py', [], 'producer'),
        ('fit_120dps', 'numerical_expansion.py',
         ['--nmax', '1000', '--dps', '120', '--training', '400,550,700'], 'producer'),
        ('fit_150dps', 'numerical_expansion.py',
         ['--nmax', '1000', '--dps', '150', '--training', '450,650,850'], 'producer'),
        ('inverse_100dps', 'verify_inverse.py', [], 'producer'),
        ('independent_exact600_and_ode', 'independent_checks.py', [], 'independent'),
        ('extensions_stability', 'extensions/verify_stability.py', [], 'extensions'),
        ('extensions_independent_obstruction', 'extensions/verify_audit.py', [], 'extensions'),
        ('extensions_r4_exact', 'extensions/verify_r4_checks.py', [], 'extensions'),
        ('extensions_independent_phase', 'extensions/verify_phase.py', [], 'extensions'),
        ('extensions_uniform_threshold', 'extensions/verify_uniform_constants.py', [], 'extensions'),
    ]
    provenance = json.loads((ROOT / 'data/provenance.json').read_text())
    summary['reference_artifact_hashes_match_provenance'] = all(
        sha(ROOT / item['file']) == item['sha256']
        for group in ('producer_artifacts', 'independent_artifacts',
                      'extension_original_artifacts', 'extension_generated_artifacts')
        for item in provenance[group])
    summary['bundled_source_hashes_match_provenance'] = all(
        sha(ROOT / item['file']) == item['bundled_sha256']
        for item in provenance['scripts'] + provenance.get('generated_scripts', []))
    success = False
    try:
        if not (summary['reference_artifact_hashes_match_provenance']
                and summary['bundled_source_hashes_match_provenance']):
            raise RuntimeError('Bundled source or reference data differ from provenance hashes.')
        for name, script, argv, destination in stages:
            print('Running ' + name + ' ...', flush=True)
            env = os.environ.copy()
            env['HISTORIC_TREE_OUTPUT_DIR'] = str(out / destination)
            env['HISTORIC_TREE_INPUT_DIR'] = str(
                out / ('extensions' if destination == 'extensions' else 'producer'))
            env['HISTORIC_TREE_REFERENCE_DIR'] = str(ROOT / 'data/extensions')
            start = time.monotonic()
            with (out / 'logs' / (name + '.log')).open('w') as log:
                result = subprocess.run([sys.executable, str(ROOT / 'code' / script), *argv],
                                        cwd=out, env=env, stdout=log, stderr=subprocess.STDOUT)
            summary['stages'].append({'name': name, 'script': 'code/' + script,
                                      'arguments': argv, 'exit_code': result.returncode,
                                      'seconds': round(time.monotonic() - start, 3),
                                      'log': 'logs/' + name + '.log'})
            if result.returncode:
                raise RuntimeError('Stage failed: ' + name + '; see its log.')
        summary['exact_artifacts'] = {p: compare(out, p) for p in EXACT_FILES}
        summary['floating_artifact_comparisons'] = {p: compare(out, p) for p in FLOAT_FILES}
        independent = json.loads((out / 'independent/independent_checks.json').read_text())
        reference = json.loads((ROOT / 'data/independent/independent_checks.json').read_text())
        summary['independent_exact_fields'] = {
            k: {'value': independent[k], 'equals_reference': independent[k] == reference[k]}
            for k in INDEPENDENT_EXACT_KEYS}
        r4 = json.loads((out / 'extensions/r4_exact_certificate.json').read_text())
        threshold = json.loads((out / 'extensions/uniform_threshold_certificate.json').read_text())
        summary['extension_exact_checks_pass'] = r4['all_exact_checks_pass']
        summary['uniform_threshold_exact_checks_pass'] = threshold['all_exact_checks_pass']
        summary['independent_exact_checks_pass'] = independent['all_exact_boolean_checks_pass']
        summary['independent_ode_success'] = independent['independent_double_precision_ode']['success']
        inverse = json.loads((out / 'producer/inverse_validation.json').read_text())
        summary['inverse_midpoint_checks_pass'] = all(
            r['midpoint_ceiling_equals_exact_integer_inverse'] for r in inverse['rows'])
        summary['exact_artifacts_match_reference'] = all(
            c['bytes_equal'] and c.get('json_equal', True)
            for c in summary['exact_artifacts'].values())
        summary['independent_exact_fields_match_reference'] = all(
            c['equals_reference'] for c in summary['independent_exact_fields'].values())
        summary['floating_outputs_identical_to_reference'] = all(
            c['bytes_equal'] and c['json_equal']
            for c in summary['floating_artifact_comparisons'].values())
        if not summary['floating_outputs_identical_to_reference']:
            summary['warnings'] = [
                'Some floating outputs differ from the reference. Inspect comparisons and logs; '
                'different platforms can change floating output. No numerical certificate is implied.']
        success = all(summary[k] for k in (
            'exact_artifacts_match_reference', 'independent_exact_fields_match_reference',
            'independent_exact_checks_pass', 'independent_ode_success', 'inverse_midpoint_checks_pass',
            'extension_exact_checks_pass', 'uniform_threshold_exact_checks_pass'))
    except Exception as exc:
        summary['error'] = str(exc)
    finally:
        after = {str(p.relative_to(ROOT)): sha(p)
                 for p in sorted((ROOT / 'data').rglob('*')) if p.is_file()}
        summary['shipped_data_unchanged'] = before == after
        summary['overall_pass'] = success and summary['shipped_data_unchanged']
        summary['finished_utc'] = dt.datetime.now(dt.timezone.utc).isoformat()
        write_json(out / 'replay_summary.json', summary)
        print('Replay output: ' + str(out))
        print('Summary: ' + str(out / 'replay_summary.json'))
        print('Exact checks / execution: ' + ('PASS' if summary['overall_pass'] else 'FAIL'))
        print('Floating evidence is non-certified, even when it matches the reference exactly.')
    return 0 if summary['overall_pass'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
