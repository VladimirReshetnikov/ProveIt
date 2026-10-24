#!/usr/bin/env python3
"""Offline release replay using Python's standard library only.

This verifies finite data and algebra, not Con(ZFC) or the unbounded ordinary
mathematical dependencies. Run from any working directory. No release files are
modified unless an explicit receipt path inside the release is requested.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
NORM_FILES = [
    'integer11_cubic_direct.json', 'integer11_cubic_centered.json',
    'integer11_mixed_direct.json', 'integer11_mixed_centered.json', 'METRICS.json',
]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def check_manifest():
    manifest = json.loads((ROOT/'MANIFEST.json').read_text())
    require(manifest['format'] == 1, 'unsupported manifest format')
    seen = set()
    for entry in manifest['files']:
        name = entry['path']
        require(name not in seen and name != 'MANIFEST.json', 'manifest duplicate/self entry')
        seen.add(name)
        path = (ROOT/name).resolve()
        require(path.is_relative_to(ROOT), 'manifest path outside release')
        require(path.is_file(), 'missing release file: '+name)
        raw = path.read_bytes()
        require(len(raw) == entry['bytes'], 'manifest size mismatch: '+name)
        require(sha256(raw) == entry['sha256'], 'manifest hash mismatch: '+name)
    require({'report.tex', 'report.pdf', 'verify_all.py', 'norm/build.py',
             'direct/equation.json', 'direct/expanded_polynomial.json'} <= seen,
            'manifest missing required deliverables')
    inherited = json.loads((ROOT/'verification/INHERITED_FILES.json').read_text())
    for entry in inherited:
        raw = (ROOT/entry['path']).read_bytes()
        require(len(raw) == entry['bytes'] and sha256(raw) == entry['sha256'],
                'inherited source mismatch: '+entry['path'])
    # The replay receipt can be added after its own run without a hash cycle.
    # Every manifest entry is still verified above, including that receipt.
    core = [entry for entry in manifest['files']
            if entry['path'] != 'verification/RELEASE_REPLAY.json']
    core.sort(key=lambda entry: entry['path'])
    return {'all_manifest_files_verified': True, 'core_release_files': len(core),
            'inherited_norm_files': len(inherited),
            'core_manifest_sha256': sha256(json.dumps(core, sort_keys=True,
                                                     separators=(',', ':')).encode()),
            'core_digest_excludes': ['MANIFEST.json', 'verification/RELEASE_REPLAY.json']}


def run_python(label, mode, script, arguments, records):
    command = [sys.executable, '-E', '-B']
    if mode:
        command.append('-O')
    command.extend([str(ROOT/script), *map(str, arguments)])
    environment = dict(os.environ)
    environment.pop('PYTHONOPTIMIZE', None)
    process = subprocess.run(command, cwd=ROOT, env=environment, text=True,
                             capture_output=True, check=False)
    if process.returncode:
        raise RuntimeError(label+' failed in '+('optimized' if mode else 'normal')+
                           ' Python:\n'+process.stdout[-6000:]+process.stderr[-6000:])
    try:
        result = json.loads(process.stdout)
    except json.JSONDecodeError as error:
        raise RuntimeError(label+' returned an invalid JSON receipt') from error
    if isinstance(result, dict):
        require(result.get('status') == 'PASS' or result.get('passed') is True,
                label+' did not report success')
    records.append({'check': label, 'optimization_level': mode, 'status': 'PASS',
                    'stdout_sha256': sha256(process.stdout.encode())})
    print('[PASS] '+label+' ('+('optimized' if mode else 'normal')+')', file=sys.stderr)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt', type=Path, help='Optional JSON receipt, preferably outside the release.')
    arguments = parser.parse_args()
    before = check_manifest()
    records, direct_metrics, norm_metrics = [], None, None
    with tempfile.TemporaryDirectory(prefix='conzfc-release-replay-') as temporary:
        temporary = Path(temporary)
        for mode in (0, 1):
            destination = temporary/('norm-'+str(mode))
            norm_metrics = run_python('norm deterministic rebuild', mode, 'norm/build.py',
                                     ['--output-dir', destination], records)
            for name in NORM_FILES:
                require((destination/name).read_bytes() == (ROOT/'norm'/name).read_bytes(),
                        'norm rebuild differs: '+name)
            run_python('six fixed numeral reconstruction', mode, 'norm/verify_coefficients.py', [], records)
            run_python('independent norm and degree audit', mode, 'norm/audit_independent.py', [], records)
            run_python('direct deterministic rebuild', mode, 'direct/build.py', ['--check'], records)
            result = run_python('independent direct expansion and projection', mode,
                                'direct/verify.py', [], records)
            direct_metrics = result['metrics']
            run_python('second direct guard and frame audit', mode,
                       'direct/independent_guard_audit.py', [ROOT/'direct'], records)
    after = check_manifest()
    require(before == after, 'release changed during verification')
    result = {
        'status': 'PASS', 'python': sys.version.split()[0],
        'manifest': before, 'checks': records,
        'norm_metrics': norm_metrics, 'direct_metrics': direct_metrics,
        'normal_and_optimized_new_checkers': True,
        'coefficient_recipe_mode': 'Unchanged inherited recipe main runs normally; its -O prohibition is preserved.',
        'release_files_unchanged': True,
        'scope': 'Exact finite artifacts and algebra. Unbounded ordinary proofs and inherited calibration are separate.',
        'new_end_to_end_proof_assistant_build': False,
    }
    output = json.dumps(result, indent=2)+'\n'
    if arguments.receipt:
        arguments.receipt.parent.mkdir(parents=True, exist_ok=True)
        arguments.receipt.write_text(output)
    print(output)


if __name__ == '__main__':
    main()
