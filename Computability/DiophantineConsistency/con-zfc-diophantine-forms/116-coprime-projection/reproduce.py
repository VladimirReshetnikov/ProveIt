#!/usr/bin/env python3
"""Rebuild and audit this release without changing its delivered files.

All work takes place in two separate temporary copies, one per Python mode.
The caller's current directory is irrelevant. Python 3.10+ and SymPy 1.14.0
are required for the complete independent audits. No network or Git clone is
used. The saved receipts document finite checks, not the unbounded theorem.
"""
from __future__ import annotations
import argparse
import ast
import hashlib
import gzip
import importlib.metadata
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
COMPONENTS = ('integer', 'positive', 'lowdegree', 'alternative')


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def snapshot(root):
    """Include all delivered regular files; refuse links and special files."""
    result = {}
    for path in sorted(root.rglob('*')):
        require(not path.is_symlink(), 'Unsupported symbolic link: ' + str(path))
        if path.is_file():
            result[path.relative_to(root).as_posix()] = digest(path)
        else:
            require(path.is_dir(), 'Unsupported filesystem object: ' + str(path))
    return result


def manifest_records(path):
    obj = json.loads(path.read_text(encoding='utf-8'))
    records = obj['files']
    if isinstance(records, dict):
        records = [dict(path=name, sha256=value) if isinstance(value, str)
                   else dict(value, path=name) for name, value in records.items()]
    require(isinstance(records, list) and records, 'Empty or invalid manifest: ' + str(path))
    seen = set()
    for item in records:
        name = item['path']
        relative = PurePosixPath(name)
        require(isinstance(name, str) and not relative.is_absolute()
                and '..' not in relative.parts and '\\' not in name,
                'Unsafe manifest path: ' + repr(name))
        require(name not in seen, 'Duplicate manifest entry: ' + name)
        seen.add(name)
        yield item


def verify_manifest(path):
    count = 0
    covered = set()
    for item in manifest_records(path):
        covered.add(item['path'])
        target = path.parent / item['path']
        require(target.is_file() and not target.is_symlink(),
                'Manifest file missing: ' + str(target))
        require(digest(target) == item['sha256'], 'Manifest digest mismatch: ' + str(target))
        if 'bytes' in item:
            require(target.stat().st_size == item['bytes'], 'Manifest size mismatch: ' + str(target))
        count += 1
    if path.parent in [ROOT / name for name in COMPONENTS]:
        require(set(snapshot(path.parent)) == covered | {path.name},
                'Component manifest has incomplete coverage or unexpected files: ' + str(path))
    return count


def verify_snapshot(root, expected):
    actual = snapshot(root)
    require(actual == expected, 'Snapshot mismatch (missing, changed, or unexpected files)')


def integrity_negative_controls(work, expected):
    """Demonstrate byte-corruption, deletion, and added-file rejection."""
    candidate = next(name for name in expected if name.endswith('equation.json'))
    target = work / candidate
    original = target.read_bytes()
    result = []
    for name in ('single_byte_change', 'missing_file', 'unexpected_file'):
        extra = work / 'UNEXPECTED_INTEGRITY_NEGATIVE_CONTROL.txt'
        if name == 'single_byte_change':
            require(bool(original), 'Empty integrity fixture')
            target.write_bytes(bytes([original[0] ^ 1]) + original[1:])
        elif name == 'missing_file':
            target.unlink()
        else:
            extra.write_text('Deliberate integrity negative control.\n', encoding='utf-8')
        try:
            verify_snapshot(work, expected)
        except RuntimeError:
            result.append(name)
        else:
            raise RuntimeError('Integrity negative control was accepted: ' + name)
        finally:
            target.write_bytes(original)
            if extra.exists():
                extra.unlink()
    verify_snapshot(work, expected)
    return result


def run_python(work, cwd, relative, mode, arguments=(), expect_failure=False):
    command = [sys.executable, '-B'] + (['-O'] if mode == 'optimized' else [])
    command += [str(work / relative), *arguments]
    env = {key: value for key, value in os.environ.items()
           if key not in ('PYTHONPATH', 'PYTHONHOME', 'PYTHONSTARTUP', 'PYTHONOPTIMIZE')}
    env.update(PYTHONDONTWRITEBYTECODE='1', PYTHONHASHSEED='0')
    process = subprocess.run(command, cwd=cwd, env=env, capture_output=True,
                             text=True, timeout=600)
    if expect_failure:
        require(process.returncode != 0,
                'Corrupted candidate unexpectedly accepted: ' + relative)
    else:
        require(process.returncode == 0,
                relative + ' failed in ' + mode + ' mode:\n' + process.stdout[-4000:]
                + process.stderr[-4000:])
    controls = {}
    if not expect_failure:
        try:
            parsed = json.loads(process.stdout)
        except (ValueError, TypeError):
            parsed = {}
        for key in ('mutations_rejected', 'rejected_mutations',
                    'deliberate_corruptions_rejected', 'nonpolynomial_mutations_rejected',
                    'witness_mutations_rejected'):
            if key in parsed:
                value = parsed[key]
                controls[key] = len(value) if isinstance(value, list) else value
    return {'script': relative, 'arguments': list(arguments),
            'mode': mode, 'exit_code': process.returncode,
            'explicit_rejected_controls': controls,
            'stdout_sha256': hashlib.sha256(process.stdout.encode()).hexdigest(),
            'stderr_sha256': hashlib.sha256(process.stderr.encode()).hexdigest(),
            **({'expected_rejection': process.stderr.strip().splitlines()[-1]}
               if expect_failure and process.stderr.strip() else {})}


def lowdegree_plan(root):
    folder = root / 'lowdegree'
    discovered = {p.relative_to(folder).as_posix()
                  for p in folder.rglob('build*.py')
                  if len(p.relative_to(folder).parts) <= 2}
    specification = folder / 'REPRODUCE_PLAN.json'
    if specification.is_file():
        variants = json.loads(specification.read_text(encoding='utf-8'))['variants']
    else:
        require(all(Path(name).name == 'build.py' for name in discovered),
                'Additional low-degree builders require REPRODUCE_PLAN.json')
        variants = [{'builder': name,
                     'outputs': [(Path(name).parent / output).as_posix()
                                 for output in ('equation.json', 'specification.json')],
                     'auditor': (Path(name).parent / 'review/audit.py').as_posix()}
                    for name in sorted(discovered)]
    require(variants and isinstance(variants, list), 'Missing low-degree reproduction plan')
    listed = [item['builder'] for item in variants]
    require(len(listed) == len(set(listed)) and set(listed) == discovered,
            'Low-degree reproduction plan does not exactly cover the active builders')
    builds, audits = [], []
    for item in variants:
        require(bool(item['outputs']), 'No declared rebuild outputs')
        paths = [item['builder'], item['auditor'], *item['outputs']]
        for name in paths:
            relative = PurePosixPath(name)
            require(not relative.is_absolute() and '..' not in relative.parts
                    and chr(92) not in name and (folder / name).is_file(),
                    'Unsafe or missing low-degree plan path: ' + name)
        builds.append(('lowdegree/' + item['builder'],
                       tuple('lowdegree/' + name for name in item['outputs'])))
        audit = 'lowdegree/' + item['auditor']
        if audit not in audits:
            audits.append(audit)
    return builds, audits


def build_plan(root):
    plan = [
        ('integer/build.py', ('integer/guard_fused11_aux.json',
                             'integer/guard_fused11_direct.json',
                             'integer/fused11_rational.json',
                             'integer/fused11_integral.json', 'integer/METRICS.json')),
        ('positive/build.py', ('positive/equation.json',)),
        ('alternative/build.py', ('alternative/POWER_ONE_9AUX.json',
                                 'alternative/POWER_TWO_13AUX.json',
                                 'alternative/POWER_TWO_14AUX.json',
                                 'alternative/FOUR_CORNER_21NAT.json',
                                 'alternative/FOUR_CORNER_22NAT.json',
                                 'alternative/METRICS.json')),
    ]
    return plan + lowdegree_plan(root)[0]


def audit_plan(root):
    plan = ['integer/check.py', 'positive/check.py', 'alternative/check.py',
            'review/integer/independent_audit.py', 'review/positive/audit.py',
            'review/alternative/audit_power_graph.py', 'baseline/check_late_evidence.py']
    # Low-degree auditors travel with the variants. The explicit plan covers
    # every active builder, including separately emitted optimized schedules.
    plan += lowdegree_plan(root)[1]
    require(all((root / relative).is_file() for relative in plan),
            'One or more required review scripts are missing')
    return plan


def mathematical_negative_controls(work, cwd, mode):
    """Corrupt an actual delivered integer DAG, outside any manifest guard."""
    relative = 'integer/guard_fused11_aux.json'
    path = work / relative
    original = path.read_bytes()
    packet = json.loads(original)
    index = packet['output']
    node = packet['nodes'][index]
    require(node[0] in ('add', 'sub', 'mul'), 'Nonarithmetic integer output')
    packet['nodes'][index][0] = 'add' if node[0] != 'add' else 'sub'
    path.write_text(json.dumps(packet, indent=2) + '\n', encoding='utf-8')
    try:
        report = run_python(work, cwd, 'integer/check.py', mode, expect_failure=True)
    finally:
        path.write_bytes(original)
    return {'mutation': 'integer actual output operation changed',
            'rejected': True, 'checker': report}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt', type=Path,
                        help='Write the JSON receipt here, after checking the original tree is unchanged.')
    args = parser.parse_args()
    if args.receipt:
        require(not args.receipt.resolve().is_relative_to(ROOT),
                'Save a new receipt outside the release to preserve its manifests')
    require(sys.version_info >= (3, 10), 'Python 3.10 or newer is required')
    try:
        version = importlib.metadata.version('sympy')
    except importlib.metadata.PackageNotFoundError as error:
        raise RuntimeError('Complete independent review requires SymPy 1.14.0; see requirements.txt') from error
    require(version == '1.14.0', 'Pinned independent review requires SymPy 1.14.0; found ' + version)
    initial = snapshot(ROOT)
    manifests = []
    for folder in [ROOT] + [ROOT / name for name in COMPONENTS]:
        for name in ('MANIFEST.json', 'MANIFEST.sha256.json'):
            path = folder / name
            if path.is_file():
                manifests.append({'path': path.relative_to(ROOT).as_posix(),
                                  'verified_files': verify_manifest(path)})
    require(all((ROOT / name).is_dir() for name in COMPONENTS), 'Incomplete component set')
    builds, audits = build_plan(ROOT), audit_plan(ROOT)
    for script in audits:
        tree = ast.parse((ROOT / script).read_text(encoding='utf-8'))
        require(not any(isinstance(node, ast.Assert) for node in ast.walk(tree)),
                'Removable assertion in an active audit: ' + script)
    receipt = {'status': 'PASS', 'python': sys.version.split()[0], 'sympy': version,
               'scope': 'Finite exact identities, literal-circuit checks, coefficient authentication, '
                        'byte-identical rebuilds, and mutation controls. The ordinary unbounded '
                        'proofs and inherited source calibration are separate dependencies. '
                        'No proof-assistant or internal-ZFC certificate is claimed.',
               'source_file_count': len(initial), 'verified_manifests': manifests,
               'optimization_safe_audit_entrypoints': len(audits),
               'modes': {}}
    with tempfile.TemporaryDirectory(prefix='diophantine-release-') as temporary:
        base = Path(temporary)
        for mode in ('normal', 'optimized'):
            work = base / mode / 'release'
            shutil.copytree(ROOT, work)
            cwd = base / mode / 'unrelated-cwd'
            cwd.mkdir()
            verify_snapshot(work, initial)
            report = {'integrity_negative_controls': integrity_negative_controls(work, initial),
                      'builds': [], 'audits': []}
            for script, outputs in builds:
                expected = {name: digest(work / name) for name in outputs}
                result = run_python(work, cwd, script, mode)
                require(all(digest(work / name) == value for name, value in expected.items()),
                        'Nonidentical rebuild: ' + script)
                result['byte_identical_outputs'] = expected
                report['builds'].append(result)
            for script in audits:
                certificates = sorted((work / script).parent.glob('*CERTIFICATE.json*'))
                def certificate_digest(path):
                    raw = path.read_bytes()
                    if path.suffix == '.gz':
                        raw = gzip.decompress(raw)
                    return hashlib.sha256(raw).hexdigest()
                expected = {path.relative_to(work).as_posix(): certificate_digest(path)
                            for path in certificates}
                result = run_python(work, cwd, script, mode)
                require(all(certificate_digest(work / name) == value
                            for name, value in expected.items()),
                        'Regenerated exact certificate differs: ' + script)
                result['identical_certificate_contents'] = expected
                report['audits'].append(result)
            report['actual_file_negative_control'] = mathematical_negative_controls(work, cwd, mode)
            receipt['modes'][mode] = report
            print(mode + ': all builds, audits, and negative controls passed', file=sys.stderr)
    verify_snapshot(ROOT, initial)
    receipt['original_release_unchanged'] = True
    raw = json.dumps(receipt, indent=2) + '\n'
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(raw, encoding='utf-8')
    print(raw, end='')


if __name__ == '__main__':
    main()
