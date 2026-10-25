#!/usr/bin/env python3
"""Offline integrated checks; no component artifacts are modified."""
from pathlib import Path
import argparse
import copy
import gzip
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read(path):
    return json.loads(path.read_text())


def manifest_check(required=False):
    path = ROOT / 'MANIFEST.sha256'
    if not path.exists():
        require(not required, 'MANIFEST.sha256 is absent')
        return {'status': 'not present during pre-seal run'}
    seen = set()
    for line in path.read_text().splitlines():
        digest, relative = line.split('  ', 1)
        require(len(digest) == 64 and all(c in '0123456789abcdef' for c in digest),
                'Malformed manifest digest')
        target = (ROOT / relative).resolve()
        require(target.is_relative_to(ROOT) and relative not in seen,
                'Unsafe or repeated manifest path')
        require(target.is_file(), 'Missing sealed file: ' + relative)
        require(hashlib.sha256(target.read_bytes()).hexdigest() == digest,
                'Release bytes changed: ' + relative)
        seen.add(relative)
    require(bool(seen), 'Empty manifest')
    return {'status': 'pass', 'files': len(seen)}


def run(script, *arguments, cwd=None):
    command = [sys.executable, '-B']
    if not __debug__:
        command.append('-O')
    command += [str(script)] + list(map(str, arguments))
    completed = subprocess.run(command, cwd=cwd or ROOT, text=True,
                               capture_output=True)
    require(completed.returncode == 0,
            'Command failed: ' + ' '.join(command) + '\n' +
            completed.stdout[-6000:] + completed.stderr[-6000:])
    return completed.stdout


def compact_rebuild(destination):
    source = ROOT / 'compact'
    target = destination / 'compact-rebuild'
    shutil.copytree(source, target, ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
    run(target / 'build.py', cwd=target)
    exact = []
    portable = []
    for filename in ('equation_87_degree323.json', 'equation_88_degree318.json'):
        old, new = read(source / filename), read(target / filename)
        old_math, new_math = copy.deepcopy(old), copy.deepcopy(new)
        for value in (old_math, new_math):
            for port in value['coefficient_binding']['ports'].values():
                port.pop('gzip_sha256')
        require(old_math == new_math, 'Compact reconstruction changed: ' + filename)
        portable.append(filename)
        if (source / filename).read_bytes() == (target / filename).read_bytes():
            exact.append(filename)
    coefficient_files = sorted((source / 'coefficients').glob('*.gz'))
    require(len(coefficient_files) == 4, 'Wrong compact coefficient file count')
    for path in coefficient_files:
        relative = path.relative_to(source)
        rebuilt = target / relative
        require(gzip.decompress(path.read_bytes()) == gzip.decompress(rebuilt.read_bytes()),
                'Compact integer reconstruction differs: ' + str(relative))
        portable.append(str(relative))
        if path.read_bytes() == rebuilt.read_bytes():
            exact.append(str(relative))
    # Validate the reconstructed payload hashes against their reconstructed circuits.
    run(target / 'verify.py', destination / 'compact-rebuilt-verification.json', cwd=target)
    return {'mathematically_identical_files': portable, 'byte_identical_files': exact,
            'reconstructed_component_verified': True}


def verify(rebuild):
    result = {'status': 'pass', 'python': sys.version.split()[0],
              'optimized': not __debug__, 'rebuild_requested': rebuild,
              'release_manifest': manifest_check(),
              'scope': 'Finite source, algebra, coefficient, circuit, reconstruction and appendix checks; unbounded proofs and inherited consistency calibration are separate.'}
    with tempfile.TemporaryDirectory(prefix='conzfc-release-check-') as directory:
        temporary = Path(directory)
        graph_receipt = temporary / 'graph.json'
        args = ['--output', graph_receipt] + (['--rebuild'] if rebuild else [])
        run(ROOT / 'graph/verify.py', *args)
        result['graph'] = read(graph_receipt)
        print('Graph: PASS (four complete coefficient lists and certificates)', flush=True)

        direct_receipt = temporary / 'direct.json'
        args = ['--receipt', direct_receipt] + (['--rebuild'] if rebuild else [])
        run(ROOT / 'direct/verify.py', *args)
        result['direct'] = read(direct_receipt)
        result['direct_independent_rows'] = json.loads(run(ROOT / 'direct/reviews/independent_raw_rows.py'))
        print('Direct: PASS (226/227 equations, projections and independent raw rows)', flush=True)

        compact_receipt = temporary / 'compact.json'
        run(ROOT / 'compact/verify.py', compact_receipt)
        result['compact'] = read(compact_receipt)
        result['compact_independent'] = {}
        for operations, degree in ((87, 323), (88, 318)):
            receipt = temporary / f'compact-independent-{operations}.json'
            run(ROOT / 'compact/review/independent_lower_center.py',
                ROOT / 'compact/upstream133/compact/equation_85.json',
                ROOT / f'compact/equation_{operations}_degree{degree}.json',
                '--coefficients', ROOT / 'compact/coefficients', '--output', receipt)
            result['compact_independent'][str(operations)] = read(receipt)
        if rebuild:
            result['compact_rebuild'] = compact_rebuild(temporary)
        print('Compact: PASS (87/323 and 88/318, all coefficients, independent algebra)', flush=True)

        result['printed_appendices'] = run(ROOT / 'generate_report_inputs.py', '--check').strip()
        print('Printed appendices: PASS', flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rebuild', action='store_true')
    parser.add_argument('--manifest-only', action='store_true')
    parser.add_argument('--receipt', type=Path)
    args = parser.parse_args()
    result = manifest_check(required=True) if args.manifest_only else verify(args.rebuild)
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(json.dumps(result, sort_keys=True, indent=2) + '\n')
    print('Release verification: PASS', flush=True)


if __name__ == '__main__':
    main()
