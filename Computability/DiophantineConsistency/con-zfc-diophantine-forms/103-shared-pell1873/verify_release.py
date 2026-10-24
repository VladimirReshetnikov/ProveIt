#!/usr/bin/env python3
"""Reproduce and audit both delivered quartics using only the standard library.

Run from any directory with ``python3 /path/to/package/verify_release.py``.
All source and equation paths are resolved relative to this file. Equation
rebuilds and checker side effects are isolated in a TemporaryDirectory.
Only named ``checks/RELEASE_*.json`` receipts are written to the package.

If SHA256SUMS exists, every listed file outside checks/ is verified before
replay. The checks/ tree contains regenerable receipts and is excluded from
that manifest check. The mathematical proofs are not replaced by this finite
release replay, and the script does not compile the supplied Lean interfaces.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent
CHECKS = ROOT / 'checks'
JSON_FILES = ('circuit.json', 'residuals.json', 'polynomial.json', 'metrics.json',
              'semantic_certificate.json', 'local_row.json')
VARIANTS = (('primary', 'equations', 16),
            ('small_height', 'equations_small_height', 1))
CHECKER_FILES = ('verify_source.py', 'verify_source_negative.py',
                 'verify_batch.py', 'verify_recurrence.py',
                 'verify_polynomial.py', 'verify_signed_index.py')


class ReleaseError(RuntimeError):
    pass


def require(condition, message):
    if not condition:
        raise ReleaseError(message)


def digest(path):
    hasher = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            hasher.update(block)
    return hasher.hexdigest()


def write_json(path, payload):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + '.new')
    temporary.write_text(json.dumps(payload, sort_keys=True, indent=2) + '\n',
                         encoding='utf-8')
    temporary.replace(path)


def verify_manifest():
    manifest = ROOT / 'SHA256SUMS'
    if not manifest.exists():
        return {'status': 'NOT_PRESENT',
                'scope': 'No optional SHA256SUMS was present; exact rebuild and independent checks still run.'}
    checked = []
    skipped = []
    seen = set()
    for number, line in enumerate(manifest.read_text(encoding='utf-8').splitlines(), 1):
        if not line.strip():
            continue
        match = re.fullmatch(r'([0-9a-fA-F]{64}) [ *](.+)', line)
        require(match is not None, 'Malformed SHA256SUMS line ' + str(number))
        expected, name = match.groups()
        relative = Path(name)
        require(not relative.is_absolute() and '..' not in relative.parts,
                'Manifest entry is not package-relative: ' + name)
        normalized = relative.as_posix()
        require(normalized not in seen, 'Duplicate manifest entry: ' + normalized)
        seen.add(normalized)
        if relative.parts and relative.parts[0] == 'checks':
            skipped.append(normalized)
            continue
        target = ROOT / relative
        require(target.resolve().is_relative_to(ROOT),
                'Manifest entry resolves outside package: ' + name)
        require(target.is_file(), 'Manifest file missing: ' + name)
        require(digest(target) == expected.lower(), 'Manifest mismatch: ' + name)
        checked.append(normalized)
    return {'status': 'PASS', 'verified_entries': len(checked),
            'excluded_receipt_entries': len(skipped),
            'manifest_sha256': digest(manifest),
            'scope': 'Every listed file outside the regenerable checks/ receipt tree; not a claim that the manifest lists every file.'}


def command(stage, script, arguments, optimized, working_directory, records):
    argv = [sys.executable, '-B'] + (['-O'] if optimized else [])
    argv += [str(script), *map(str, arguments)]
    environment = dict(os.environ)
    environment['PYTHONDONTWRITEBYTECODE'] = '1'
    environment.pop('PYTHONPATH', None)
    try:
        result = subprocess.run(argv, cwd=working_directory, env=environment,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                text=True, encoding='utf-8', timeout=120,
                                check=False)
    except subprocess.TimeoutExpired as error:
        raise ReleaseError(stage + ' exceeded its 120-second stage timeout') from error
    record = {'stage': stage, 'script': script.name,
              'optimized_python': optimized, 'returncode': result.returncode,
              'stdout_sha256': hashlib.sha256(result.stdout.encode('utf-8')).hexdigest(),
              'stderr_sha256': hashlib.sha256(result.stderr.encode('utf-8')).hexdigest(),
              'stdout_bytes': len(result.stdout.encode('utf-8')),
              'stderr_bytes': len(result.stderr.encode('utf-8'))}
    records.append(record)
    if result.returncode:
        detail = (result.stderr or result.stdout).strip()[-2400:]
        raise ReleaseError(stage + ' failed (exit ' + str(result.returncode) + '):\n' + detail)
    print('PASS ' + stage, flush=True)
    return result


def load_pass(path, stage):
    require(path.is_file(), 'Checker omitted its receipt: ' + stage)
    try:
        result = json.loads(path.read_text(encoding='utf-8'))
    except (ValueError, OSError) as error:
        raise ReleaseError('Invalid checker receipt: ' + stage) from error
    require(result.get('status') == 'PASS', 'Checker receipt is not PASS: ' + stage)
    return result


def save_receipt(source, destination_name, receipts):
    payload = source.read_bytes()
    target = CHECKS / destination_name
    temporary = target.with_name(target.name + '.new')
    temporary.write_bytes(payload)
    temporary.replace(target)
    receipts.append({'path': target.relative_to(ROOT).as_posix(),
                     'sha256': hashlib.sha256(payload).hexdigest()})


def replay():
    CHECKS.mkdir(exist_ok=True)
    manifest = verify_manifest()
    records, receipts, rebuilds = [], [], []
    for name in ('build.py', *CHECKER_FILES):
        require((ROOT / name).is_file(), 'Missing release program: ' + name)
    for _, directory, _ in VARIANTS:
        for name in JSON_FILES:
            require((ROOT / directory / name).is_file(),
                    'Missing delivered equation artifact: ' + directory + '/' + name)
    # The two flattenings must start from precisely the same semantic source.
    for name in ('semantic_certificate.json', 'local_row.json', 'circuit.json'):
        require((ROOT / 'equations' / name).read_bytes()
                == (ROOT / 'equations_small_height' / name).read_bytes(),
                'Variants disagree before flattening: ' + name)

    with tempfile.TemporaryDirectory(prefix='con-zfc-release-') as temporary:
        work = Path(temporary)
        for optimized in (False, True):
            mode = 'optimized' if optimized else 'normal'
            for variant, directory, affine_cap in VARIANTS:
                regenerated = work / ('build_' + variant + '_' + mode)
                stage = 'rebuild ' + variant + ' ' + mode
                command(stage, ROOT / 'build.py',
                        ['--output', regenerated, '--affine-cap', affine_cap],
                        optimized, ROOT, records)
                found = {p.name for p in regenerated.iterdir() if p.is_file()}
                require(found == set(JSON_FILES), 'Unexpected rebuild output inventory: ' + stage)
                compared = []
                for name in JSON_FILES:
                    reference, candidate = ROOT / directory / name, regenerated / name
                    require(reference.read_bytes() == candidate.read_bytes(),
                            'Rebuilt bytes differ: ' + directory + '/' + name + ' (' + mode + ')')
                    compared.append({'path': directory + '/' + name, 'sha256': digest(reference),
                                     'bytes': reference.stat().st_size})
                rebuilds.append({'variant': variant, 'optimized_python': optimized,
                                 'status': 'PASS', 'byte_equal_files': compared})

        for optimized in (False, True):
            mode = 'optimized' if optimized else 'normal'
            suffix = mode.upper()
            # These two check the common semantic graph, byte-identical in both variants.
            source_receipt = work / ('source_' + mode + '.json')
            command('source ' + mode, ROOT / 'verify_source.py',
                    [ROOT, '--output', source_receipt], optimized, ROOT, records)
            source = load_pass(source_receipt, 'source ' + mode)
            require(source.get('complete_source_prefix_equalities') == 57,
                    'Unexpected source equality coverage')
            require(source.get('unconditionally_positive_power_bases') == 40
                    and source.get('unconditionally_positive_power_exponents') == 40,
                    'Power argument positivity coverage is incomplete')
            save_receipt(source_receipt, 'RELEASE_SOURCE_' + suffix + '.json', receipts)

            source_negative_receipt = work / ('source_negative_' + mode + '.json')
            command('source negative controls ' + mode, ROOT / 'verify_source_negative.py',
                    ['--package', ROOT, '--output', source_negative_receipt],
                    optimized, ROOT, records)
            source_negative = load_pass(source_negative_receipt,
                                        'source negative controls ' + mode)
            source_controls = source_negative.get('controls', [])
            require(len(source_controls) == 3
                    and all(c.get('status') == 'REJECTED' for c in source_controls),
                    'All three source negative controls must be rejected')
            require(source_negative.get('unmodified_source') == 'PASS'
                    and source_negative.get('copied_unmodified_source') == 'PASS',
                    'Source negative controls lack unmodified positive controls')
            save_receipt(source_negative_receipt,
                         'RELEASE_SOURCE_NEGATIVE_' + suffix + '.json', receipts)

            batch_receipt = work / ('batch_' + mode + '.json')
            command('batch ' + mode, ROOT / 'verify_batch.py',
                    [ROOT / 'equations' / 'semantic_certificate.json',
                     '--negative-controls', '--output', batch_receipt],
                    optimized, ROOT, records)
            batch = load_pass(batch_receipt, 'batch ' + mode)
            controls = batch.get('negative_controls', [])
            require(len(controls) == 17 and all(c.get('rejected') is True for c in controls),
                    'All seventeen batch negative controls must be rejected')
            require((batch.get('power_calls'), batch.get('distinct_exponents'),
                     batch.get('seed_indices'), batch.get('derived_indices')) == (40, 19, 16, 3),
                    'Unexpected batch inventory')
            save_receipt(batch_receipt, 'RELEASE_BATCH_' + suffix + '.json', receipts)

            for variant, directory, _ in VARIANTS:
                path = ROOT / directory
                recurrence_receipt = work / ('recurrence_' + variant + '_' + mode + '.json')
                command('recurrence ' + variant + ' ' + mode, ROOT / 'verify_recurrence.py',
                        ['--equations', path, '--output', recurrence_receipt],
                        optimized, ROOT, records)
                recurrence = load_pass(recurrence_receipt, 'recurrence ' + variant + ' ' + mode)
                require(recurrence.get('seed_count') == 16
                        and len(recurrence.get('recurrence_relations', [])) == 3,
                        'Incomplete recurrence coverage')
                save_receipt(recurrence_receipt,
                             'RELEASE_RECURRENCE_' + variant.upper() + '_' + suffix + '.json', receipts)

                polynomial_receipt = work / ('polynomial_' + variant + '_' + mode + '.json')
                command('polynomial ' + variant + ' ' + mode, ROOT / 'verify_polynomial.py',
                        [path, '--output', polynomial_receipt], optimized, ROOT, records)
                polynomial = load_pass(polynomial_receipt, 'polynomial ' + variant + ' ' + mode)
                require(polynomial.get('optimized_python') is optimized,
                        'Polynomial checker ran in the wrong Python mode')
                expected_variables = 1873 if variant == 'primary' else 3292
                require(polynomial.get('metrics', {}).get('ordinary_polynomial_variables') == expected_variables,
                        'Unexpected delivered variable count for ' + variant)
                save_receipt(polynomial_receipt,
                             'RELEASE_POLYNOMIAL_' + variant.upper() + '_' + suffix + '.json', receipts)

            # This finite diagnostic writes beside __file__ and has no input-file
            # argument. Run an exact byte copy in private scratch so it cannot
            # overwrite a pre-existing package receipt. It has no local imports.
            finite_dir = work / ('signed_index_' + mode)
            finite_dir.mkdir()
            finite_script = finite_dir / 'verify_signed_index.py'
            shutil.copyfile(ROOT / 'verify_signed_index.py', finite_script)
            require(digest(finite_script) == digest(ROOT / 'verify_signed_index.py'),
                    'Signed-index diagnostic copy differs from the delivered script')
            command('signed index finite controls ' + mode, finite_script, [],
                    optimized, finite_dir, records)
            finite_receipt = finite_dir / 'SIGNED_INDEX_FINITE_CHECKS.json'
            finite = load_pass(finite_receipt, 'signed index finite controls ' + mode)
            require(len(finite.get('accepted_sign_counts', {})) == 4
                    and all(n > 0 for n in finite['accepted_sign_counts'].values()),
                    'The signed diagnostic did not exercise all four sign combinations')
            require(finite.get('negative_control', {}).get('wrong_index_admitted') is True,
                    'Missing essential squared-divisibility negative control')
            save_receipt(finite_receipt, 'RELEASE_SIGNED_INDEX_' + suffix + '.json', receipts)

    metrics = {variant: json.loads((ROOT / directory / 'metrics.json').read_text(encoding='utf-8'))
               for variant, directory, _ in VARIANTS}
    return {'status': 'PASS', 'scope':
            'Exact deterministic reconstruction of both supplied equations, source and domain interfaces, '
            'all 75 shared-certificate equalities, three exponent recurrences, full register/guard restoration, '
            'and every collected polynomial coefficient. Signed-index sweeps are finite diagnostics. '
            'The universal consistency theorem additionally uses the supplied ordinary proofs; '
            'no Lean or object-language ZFC proof is compiled here.',
            'python_version': '.'.join(map(str, sys.version_info[:3])),
            'manifest': manifest,
            'rebuilds': rebuilds, 'subprocess_stages': records,
            'subprocess_stage_count': len(records),
            'independent_checker_runs': len(receipts),
            'source_negative_controls_per_mode': 3,
            'batch_negative_controls_per_mode': 17,
            'checks_run_in_normal_and_optimized_python': list(CHECKER_FILES),
            'metrics': metrics, 'receipts': receipts,
            'program_sha256': {name: digest(ROOT / name) for name in
                               ('verify_release.py', 'build.py', *CHECKER_FILES)},
            'receipt_policy': 'Only checks/RELEASE_*.json are regenerated. Exclude the checks/ receipt tree from immutable manifest verification.'}


def main():
    try:
        result = replay()
    except Exception as error:
        result = {'status': 'FAIL', 'error_type': type(error).__name__, 'error': str(error),
                  'scope': 'Release replay failed; no successful verification is claimed.'}
        write_json(CHECKS / 'RELEASE_VERIFY.json', result)
        print(json.dumps(result, sort_keys=True, indent=2), file=sys.stderr)
        return 1
    write_json(CHECKS / 'RELEASE_VERIFY.json', result)
    print(json.dumps({'status': 'PASS', 'subprocess_stages': result['subprocess_stage_count'],
                      'checker_runs': result['independent_checker_runs'],
                      'rebuilt_files_compared': sum(len(r['byte_equal_files']) for r in result['rebuilds']),
                      'source_negative_controls_per_mode': 3,
                      'batch_negative_controls_per_mode': 17,
                      'primary_variables': result['metrics']['primary']['ordinary_polynomial_variables'],
                      'small_height_variables': result['metrics']['small_height']['ordinary_polynomial_variables'],
                      'receipt': 'checks/RELEASE_VERIFY.json'}, indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
