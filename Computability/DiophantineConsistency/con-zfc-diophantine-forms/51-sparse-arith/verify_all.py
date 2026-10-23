#!/usr/bin/env python3
"""Verify the assembled release without changing any delivered artifact.

All builders run in temporary copies. Python's standard library is sufficient.
Finite audit receipts do not replace the inherited unbounded mathematical
theorems identified in the proofs and README.
"""
from pathlib import Path
import gzip
import hashlib
import json
import platform
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def snapshot(root, directories, files):
    paths = [root / p for p in files]
    for directory in directories:
        paths += [p for p in (root / directory).rglob('*') if p.is_file()]
    return {p.relative_to(root).as_posix(): digest(p) for p in paths}


def compare(root, expected, label):
    different = [p for p, sha in expected.items()
                 if not (root / p).is_file() or digest(root / p) != sha]
    require(not different, label + ' differs: ' + ', '.join(different))


def execute(root, script, optimized=False):
    command = [sys.executable]
    if optimized:
        command.append('-O')
    command.append(str(root / script))
    result = subprocess.run(command, cwd=root, text=True, capture_output=True)
    mode = '-O' if optimized else 'normal'
    require(result.returncode == 0,
            script + ' (' + mode + ') failed:\n' + result.stdout + result.stderr)
    return {'script': script, 'mode': mode, 'status': 'PASS'}, result.stdout


def verify_jones_sources():
    manifest = json.loads((ROOT / 'provenance/JONES_SOURCES.json').read_text())
    snapshot_root = ROOT / 'upstream/JONES_RATIO_LEAN'
    modules = {}
    for row in manifest['files']:
        path = ROOT / row['file']
        data = path.read_bytes()
        require(hashlib.sha256(data).hexdigest() == row['sha256'],
                'Jones source hash mismatch: ' + row['file'])
        git_hash = hashlib.sha1(('blob ' + str(len(data)) + '\0').encode() + data).hexdigest()
        require(git_hash == row['git_blob_sha1'],
                'Jones source Git blob mismatch: ' + row['file'])
        if path.suffix == '.lean':
            name = '.'.join(path.relative_to(snapshot_root).with_suffix('').parts)
            modules[name] = data.decode()
    require(len(modules) == manifest['theorem_sources'] == 20,
            'Jones local source count')
    external = set()
    for name, source in modules.items():
        require(not re.search(r'\b(?:axiom|sorry|admit|unsafe)\b', source),
                'Jones source contains a flagged lexical token: ' + name)
        for line in source.splitlines():
            match = re.match(r'^\s*import\s+(.*)$', line)
            if match:
                for dependency in match.group(1).split('--', 1)[0].split():
                    if dependency == 'Mathlib' or dependency.startswith('Mathlib.'):
                        external.add(dependency)
                    else:
                        require(dependency in modules,
                                'Missing local Jones import: ' + dependency)
    entry = modules['Diophantine.Paper1982.NineRatio']
    for theorem in ('ratio_sound', 'ratio_complete'):
        require(re.search(r'\btheorem\s+' + theorem + r'\b', entry) is not None,
                'Missing inherited ratio theorem: ' + theorem)
    return {'status': 'PASS', 'pinned_files': len(manifest['files']),
            'local_lean_files': len(modules), 'all_local_imports_present': True,
            'flagged_lexical_tokens': 0, 'external_mathlib_imports': sorted(external),
            'new_lean_kernel_run': False}


def main():
    provenance = json.loads((ROOT / 'provenance/COEFFICIENT_SOURCES.json').read_text())
    for row in provenance['files']:
        require(digest(ROOT / row['file']) == row['sha256'],
                'Copied source pin mismatch: ' + row['file'])
    jones = verify_jones_sources()

    _, core_text = execute(ROOT, 'verify_release.py')
    core = json.loads(core_text)
    require(core['status'] == 'PASS', 'core verification did not pass')

    short_before = snapshot(ROOT / 'short', ['generated', 'coefficients/coefficients'],
                            ['coefficients/COEFFICIENT_BINDING.json',
                             'coefficients/INDEPENDENT_AUDIT.json'])
    native_before = snapshot(ROOT / 'coefficients/native31', ['payloads'],
                             ['COEFFICIENT_BINDING.json'])
    runs = []
    with tempfile.TemporaryDirectory(prefix='proveit_consistency_assembly_') as tmp:
        temporary = Path(tmp)
        short = temporary / 'short'
        native = temporary / 'native31'
        ignore = shutil.ignore_patterns('__pycache__', '*.pyc')
        shutil.copytree(ROOT / 'short', short, ignore=ignore)
        shutil.copytree(ROOT / 'coefficients/native31', native, ignore=ignore)

        record, _ = execute(native, 'build_coefficients.py')
        record['script'] = 'coefficients/native31/' + record['script']
        runs.append(record)
        compare(native, native_before, 'Native package31 regeneration')
        for name in ('beta', 'K', 'MC', 'MF_source'):
            rebuilt = gzip.decompress((native / 'payloads' / (name + '.bin.gz')).read_bytes())
            bound = gzip.decompress((ROOT / 'coefficients/payloads' / (name + '.bin.gz')).read_bytes())
            require(rebuilt == bound, 'Core native tuple disagrees with compiler: ' + name)

        for script in ('coefficients/build_coefficients.py',
                       'coefficients/audit_coefficients.py', 'build_and_audit.py'):
            record, _ = execute(short, script)
            record['script'] = 'short/' + record['script']
            runs.append(record)
        for script in ('coefficients/audit_coefficients.py', 'build_and_audit.py'):
            record, _ = execute(short, script, optimized=True)
            record['script'] = 'short/' + record['script']
            runs.append(record)
        compare(short, short_before, 'Short-circuit and package36 regeneration')
        audit = json.loads((short / 'generated/AUDIT.json').read_text())
        short_metrics = {name: {key: row[key] for key in
                         ('operations', 'exact_degree', 'witnesses', 'fixed_ports')}
                         for name, row in audit['circuits'].items()}

    # The source release is read only throughout this wrapper and its builders.
    compare(ROOT / 'short', short_before, 'Original short artifacts')
    compare(ROOT / 'coefficients/native31', native_before, 'Original native artifacts')
    print(json.dumps({
        'status': 'PASS',
        'python_version': platform.python_version(),
        'pinned_coefficient_and_notice_files': len(provenance['files']),
        'core': core,
        'additional_runs': runs,
        'additional_reproduced_files': len(short_before) + len(native_before),
        'native31_payloads_match_core': 4,
        'inherited_jones_source_audit': jones,
        'short': short_metrics,
        'release_files_modified': False,
        'scope': 'Exact finite identities, byte bindings, regeneration, liveness '
                 'and degree certificates. Unbounded compiler, Pell, Sun and '
                 'Jones results retain the mathematical proof status stated '
                 'in the accompanying dependency notes.'
    }, indent=2))


if __name__ == '__main__':
    main()
