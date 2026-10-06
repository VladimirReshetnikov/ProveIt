#!/usr/bin/env python3
"""Reproduce mandatory standard-library checks in normal and optimized Python.

By default, independent C++ TSVs are precomputed inputs checked mathematically.
--optional-cpp additionally compiles and reruns their exhaustive enumerators.
All output locations are new directories; the source package is never changed.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).absolute().parent))
import verify_manifest as manifest
import verify_frozen_sources

ROOT = Path(__file__).absolute().parent
REFERENCES = {
    'exact_checks.json': 'certificates/exact_checks.json',
    'constant_certificate.json': 'code/constant_certificate.json',
    'effective_error_checks.json': 'certificates/effective_error_checks.json',
    'decimal_diagnostics.json': 'certificates/decimal_diagnostics.json',
    'precomputed_audit_checks.json': 'certificates/precomputed_audit_checks.json'}
SCRIPTS = ('check_fixed_permanent.py', 'certify_constants.py',
           'test_certified_guards.py', 'check_effective_error.py',
           'decimal_diagnostics.py', 'check_precomputed_audits.py',
           'test_reproduction_guards.py')


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def run_script(root, name, destination, optimized):
    bootstrap = ('import runpy,sys; from pathlib import Path; '
                 'script=sys.argv.pop(1); sys.path.insert(0,str(Path(script).parent)); '
                 'sys.argv=[script]; runpy.run_path(script,run_name="__main__")')
    command = [sys.executable, '-I', '-S', '-B']+(['-O'] if optimized else [])
    command += ['-c', bootstrap, str(root/'code'/name)]
    env = {'PATH': os.defpath, 'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8',
           'PYTHONHASHSEED': '0', 'PYTHONDONTWRITEBYTECODE': '1'}
    process = subprocess.run(command, cwd=destination, env=env, capture_output=True,
                             text=True, timeout=900, shell=False)
    require(process.returncode == 0 and (name == 'certify_constants.py' or 'PASS' in process.stdout),
            name+' failed:\n'+(process.stdout+process.stderr)[-12000:])
    return process.stdout


def optional_cpp(root, destination):
    compiler = shutil.which('g++')
    require(compiler is not None, '--optional-cpp requires g++ with C++17 support')
    destination.mkdir(exist_ok=False)
    for stem, table in [('audit_counts', 'audit_counts.tsv'), ('audit_blocks', 'audit_block_counts.tsv')]:
        binary = destination/stem
        for command in ([compiler, '-O3', '-std=c++17', '-UNDEBUG', str(root/'optional'/(stem+'.cpp')), '-o', str(binary)],
                        [str(binary)]):
            result = subprocess.run(command, cwd=destination, capture_output=True,
                                    text=True, timeout=900, shell=False)
            require(result.returncode == 0, 'optional exhaustive audit failed:\n'+result.stderr)
        require((destination/table).read_bytes() == (root/'optional'/table).read_bytes(),
                'optional C++ output differs: '+table)
    return {'status': 'PASS', 'exhaustive_cpp_rerun': True,
            'output_tables_match_frozen_bytes': True,
            'compiler': 'g++ -O3 -std=c++17 -UNDEBUG'}


def run(root, output_dir, include_cpp=False):
    root = manifest.check_directory(root)
    provenance = verify_frozen_sources.verify(root)
    output_dir = Path(output_dir).absolute()
    require('..' not in output_dir.parts, 'unsafe output directory')
    manifest.check_directory(output_dir.parent)
    require(not os.path.lexists(output_dir), 'reproduction output already exists')
    require(not output_dir.resolve().is_relative_to(root.resolve()), 'output must be outside source package')
    output_dir.mkdir(exist_ok=False)
    guards = []
    for mode, optimized in [('normal', False), ('optimized', True)]:
        destination = output_dir/mode
        destination.mkdir()
        for name in SCRIPTS:
            output = run_script(root, name, destination, optimized)
            if name == 'test_reproduction_guards.py':
                guards.append(manifest.load_json(output))
        actual = {p.name for p in destination.iterdir()}
        require(actual == set(REFERENCES), mode+' output inventory differs')
        for name, reference in REFERENCES.items():
            require(manifest.read_regular(destination/name) == manifest.read_regular(root/reference),
                    mode+' byte mismatch: '+name)
    require(guards[0] == guards[1], 'normal and optimized corruption guards differ')
    result = {'status': 'PASS', 'standard_library_only': True,
              'normal_and_optimized_identical_to_reference': True,
              'certificate_guard_negative_tests_per_mode': 9,
              'additional_reproduction_guards': guards[0],
              'reference_file_count': len(REFERENCES),
              'reference_sha256': {name: hashlib.sha256(manifest.read_regular(root/path)).hexdigest()
                                   for name, path in sorted(REFERENCES.items())},
              'frozen_sources': provenance,
              'decimal_values_are_diagnostics_not_certificates': True,
              'optional_cpp': {'exhaustive_cpp_rerun': False, 'mode': 'precomputed tables checked'}}
    if include_cpp:
        result['optional_cpp'] = optional_cpp(root, output_dir/'cpp')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, help='new directory outside package; parent must exist')
    parser.add_argument('--optional-cpp', action='store_true', help='also compile and rerun exhaustive C++ checks')
    args = parser.parse_args()
    try:
        if args.output_dir is not None:
            result = run(ROOT, args.output_dir, args.optional_cpp)
        else:
            with tempfile.TemporaryDirectory(prefix='report184-replay-') as temporary:
                result = run(ROOT, Path(temporary)/'results', args.optional_cpp)
        print(json.dumps(result, sort_keys=True, indent=2))
    except (ArithmeticError, ValueError, OSError, subprocess.TimeoutExpired) as exc:
        print(json.dumps({'status': 'FAIL', 'error': str(exc)}, sort_keys=True), file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
