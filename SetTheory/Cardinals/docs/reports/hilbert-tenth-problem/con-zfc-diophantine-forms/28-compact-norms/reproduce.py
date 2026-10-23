#!/usr/bin/env python3
"""Rebuild and verify this release offline using the Python standard library.

All construction and optional coefficient outputs are written in a temporary
directory. Only verification/REPRODUCED.json is updated in the release.
This checks finite algebraic artifacts; see report.pdf for the quantified
proof and inherited theorem boundary.
"""
from __future__ import annotations

import argparse
import gzip
from hashlib import sha256
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent
PIN = 'ae3007ca4467011e0e051c84acb4a1dd13971b0e'


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(data):
    return sha256(data).hexdigest()


def check_sources():
    records = json.loads((ROOT / 'SOURCE_MANIFEST.json').read_text())['files']
    for row in records:
        data = (ROOT / row['local_path']).read_bytes()
        require(digest(data) == row['sha256'], 'Retained source differs: ' + row['local_path'])
    return len(records)


def check_compact_manifest():
    directory = ROOT / 'compiler'
    records = json.loads((directory / 'COMPACT_PAYLOAD_MANIFEST.json').read_text())
    for row in records:
        data = (directory / row['path']).read_bytes()
        require(len(data) == row['bytes'] and digest(data) == row['sha256'],
                'Published compact payload differs: ' + row['path'])
    return len(records)


def check_coefficients(directory):
    binding = json.loads((directory / 'COMPACT_COEFFICIENT_BINDING.json').read_text())
    output = []
    for row in binding['files']:
        zipped = (directory / (row['path'] + '.gz')).read_bytes()
        require(digest(zipped) == row['gzip_sha256'], 'Compressed coefficient differs: ' + row['name'])
        raw = gzip.decompress(zipped)
        require(len(raw) == row['bytes'] and digest(raw) == row['sha256'],
                'Raw coefficient differs: ' + row['name'])
        output.append({'name': row['name'], 'bytes': len(raw), 'sha256': digest(raw)})
    return output


def run_script(work, script, *arguments):
    print('Checking ' + script, flush=True)
    command = [sys.executable, '-B', str(work / script), *map(str, arguments)]
    result = subprocess.run(command, cwd=work, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(script + ' failed:\n' + result.stdout + '\n' + result.stderr)
    require(not result.stderr.strip(), script + ' emitted unexpected stderr:\n' + result.stderr)
    return result.stdout


def compare_json(original, regenerated):
    require(original.read_bytes() == regenerated.read_bytes(),
            'Regenerated JSON bytes differ: ' + str(original.relative_to(ROOT)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rebuild-coefficients', action='store_true',
                        help='also rebuild all tiles and raw compact coefficients, then run both upstream independent audits')
    args = parser.parse_args()
    print('Authenticating pinned sources and coefficient payloads', flush=True)
    source_count = check_sources()
    payload_count = check_compact_manifest()
    coefficients = check_coefficients(ROOT / 'compiler')
    coefficient_audits = []
    with tempfile.TemporaryDirectory(prefix='con-zfc-synthesis-') as temporary:
        work = Path(temporary)
        for directory in ('code', 'vendor', 'compiler', 'audit'):
            shutil.copytree(ROOT / directory, work / directory,
                            ignore=shutil.ignore_patterns('__pycache__', '*.pyc', '*.bin'))
        (work / 'circuits').mkdir()
        if args.rebuild_coefficients:
            for script in (
                'compiler/build_wang943.py',
                'compiler/check_wang_helices.py',
                'audit/audit_wang943_independent.py',
                'compiler/build_wang943_compact.py',
                'compiler/materialize_wang943_compact.py',
                'audit/audit_wang943_compact_independent.py',
            ):
                output = run_script(work, script)
                coefficient_audits.append({'script': script, 'status': 'PASS',
                                           'stdout_sha256': digest(output.encode())})
            require(check_coefficients(work / 'compiler') == coefficients,
                    'Rebuilt coefficient binding differs')
            for row in json.loads((ROOT / 'compiler/COMPACT_PAYLOAD_MANIFEST.json').read_text()):
                data = (work / 'compiler' / row['path']).read_bytes()
                require(digest(data) == row['sha256'], 'Rebuilt compact artifact differs: ' + row['path'])

        run_script(work, 'code/build_compact12.py')
        compared = []
        for kind in ('system', 'product', 'sos'):
            relative = Path('circuits') / ('compact12_' + kind + '.json')
            compare_json(ROOT / relative, work / relative)
            compared.append(str(relative))
        compact = json.loads(run_script(work, 'code/verify_compact12.py', work / 'circuits'))
        require(compact['status'] == 'PASS', 'Independent compact verifier failed')
        require(compact == json.loads((ROOT / 'verification/INDEPENDENT_COMPACT12_CHECKS_OPTIMIZED.json').read_text()),
                'Independent compact receipt differs')

        parent = work / 'vendor/jones18/quartic32.upstream.json'
        generated = work / 'circuits/nine'
        nine_builder = json.loads(run_script(work, 'code/nine_structured.py', parent, generated))
        run_script(work, 'code/verify_structured.py', parent, generated,
                   work / 'compiler/coefficients_compact')
        for name in ('constants.json', 'index_bound_s.json', 'shifted_quartic.json',
                     'nine_structured_dag.json', 'verification.json'):
            relative = Path('circuits/nine') / name
            compare_json(ROOT / relative, work / relative)
            compared.append(str(relative))
        nine = json.loads((generated / 'verification.json').read_text())
        require(nine['status'] == 'PASS', 'Nine-variable verifier failed')

    receipt = {
        'status': 'PASS',
        'repository_revision': PIN,
        'scope': 'Offline exact regeneration and finite algebraic checks; quantified semantics rely on the ordinary proofs and inherited theorem interfaces in report.pdf. No consistency conclusion or new end-to-end kernel check.',
        'retained_source_files_authenticated': source_count,
        'published_compact_payload_records_authenticated': payload_count,
        'coefficient_bytes_authenticated': coefficients,
        'coefficient_rebuild_requested': args.rebuild_coefficients,
        'coefficient_rebuild_steps': coefficient_audits,
        'exact_json_files_compared': compared,
        'compact12_independent': compact,
        'nine_builder': nine_builder,
        'nine_verification': nine,
    }
    destination = ROOT / 'verification/REPRODUCED.json'
    destination.write_text(json.dumps(receipt, indent=2) + '\n')
    print('PASS: exact reconstruction of both constructions and all requested checks.')
    print('Receipt: verification/REPRODUCED.json')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        raise SystemExit(1)
