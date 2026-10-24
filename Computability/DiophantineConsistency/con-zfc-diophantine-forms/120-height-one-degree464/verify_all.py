#!/usr/bin/env python3
"""Offline release replay. Python standard library only.

Checks the sealed manifest, then works in a temporary copy so shipped files
and historical receipts remain unchanged. Mathematical scope: exact finite
artifact verification, with unbounded source calibration proved in the report.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt', type=Path, help='Optional JSON result path')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    manifest_path = root / 'RELEASE_MANIFEST.json'
    manifest = json.loads(manifest_path.read_text())
    checked = 0
    for name, info in manifest['files'].items():
        path = root / name
        require(path.is_file(), 'Missing release file: ' + name)
        require(path.stat().st_size == info['bytes'], 'Release byte count: ' + name)
        require(digest(path) == info['sha256'], 'Release hash: ' + name)
        checked += 1
    result = {'status': 'PASS', 'manifest_files_checked': checked,
              'repository_commit': manifest['repository_commit'], 'checks': []}
    environment = dict(os.environ)
    environment['PYTHONDONTWRITEBYTECODE'] = '1'

    with tempfile.TemporaryDirectory(prefix='con_zfc_replay_') as temp:
        work = Path(temp) / 'packet'
        shutil.copytree(root, work, ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))

        def run(label, command, directory):
            completed = subprocess.run(command, cwd=directory, env=environment,
                                       text=True, stdout=subprocess.PIPE,
                                       stderr=subprocess.STDOUT, timeout=180)
            require(completed.returncode == 0,
                    label + ' failed:\n' + completed.stdout[-16000:])
            result['checks'].append({'name': label, 'status': 'PASS'})

        height = work / 'height_one'
        for optimized in (False, True):
            mode = 'optimized' if optimized else 'normal'
            receipt = height / ('release_' + mode + '.json')
            command = [sys.executable, '-B'] + (['-O'] if optimized else [])
            command += ['verify.py', '--receipt', str(receipt)]
            run('height_one_' + mode, command, height)
            data = json.loads(receipt.read_text())
            require(data['status'] == 'PASS' and data['variables'] == 7431
                    and data['expanded_monomials_checked'] == 34086,
                    'Height-one release dimensions')
            require(len(data['rejected_artifact_controls']) == 2,
                    'Full rejected-artifact controls')
            if not optimized:
                result['height_one'] = data
        rebuilt = height / 'rebuilt'
        run('height_one_regeneration',
            [sys.executable, '-B', 'build.py', '--out', str(rebuilt)], height)
        for name in ['polynomial.json', 'certificate.json', 'METRICS.json']:
            require((rebuilt / name).read_bytes() == (height / 'output' / name).read_bytes(),
                    'Byte-identical height-one regeneration: ' + name)
        result['checks'].append({'name': 'height_one_byte_comparison', 'status': 'PASS'})

        eleven = work / 'eleven'
        for optimized in (False, True):
            mode = 'optimized' if optimized else 'normal'
            command = [sys.executable, '-B'] + (['-O'] if optimized else []) + ['check.py']
            run('eleven_' + mode, command, eleven)
            receipt = eleven / ('CHECK_OPTIMIZED.json' if optimized else 'CHECK.json')
            data = json.loads(receipt.read_text())
            require(data['status'] == 'PASS' and data['exact_artifact_regeneration'],
                    'Eleven-variable exact checks')
            if not optimized:
                result['eleven'] = {
                    'source_files_authenticated': data['source_files_authenticated'],
                    'coefficient_payloads_authenticated': data['coefficients']['payloads_authenticated'],
                    'whole_coefficient_recipe_rebuilt': data['coefficients']['recipe_rebuilt'],
                    'universal': data['universal'],
                    'equations': [{k: e[k] for k in ('name', 'topology', 'degree', 'actual_DAG_leading')}
                                  for e in data['equations']]}
    result['scope'] = ('Exact finite polynomial, circuit, coefficient, provenance, '
                       'and reproducibility checks. Unbounded calibration is inherited '
                       'and proved in the cited mathematical sources; no consistency test.')
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'status': 'PASS', 'manifest_files_checked': checked,
                      'checks': result['checks'], 'height_one': [7431, 4, 34086, 1],
                      'eleven': [[11, 464, 122], [11, 488, 121]]}, indent=2))


if __name__ == '__main__':
    main()
