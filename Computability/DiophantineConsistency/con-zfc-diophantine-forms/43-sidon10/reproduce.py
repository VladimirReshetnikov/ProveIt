#!/usr/bin/env python3
"""Rebuild and independently audit the complete delivered B2 instance.

Python standard library only. This script resolves every path relative to
itself and can be invoked from any working directory. PDF compilation is
separate: use `make pdf` when a TeX installation is available.
"""
from pathlib import Path
import hashlib
import gzip
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
GENERATED = ROOT / 'generated'


def verify_active_binding():
    instance = json.loads((ROOT / 'INSTANCE.json').read_text())
    binding = json.loads((ROOT / 'data/coefficients_binding.json').read_text())
    if not instance['authoritative_binding']:
        raise SystemExit('INSTANCE.json must be the authoritative active binding.')
    if instance['coefficient_tuple']['variant'] != binding['variant']:
        raise SystemExit('INSTANCE.json and the payload binding name different tuples.')
    expected = {row['name']: row for row in binding['files']}
    seen = set()
    for row in instance['coefficient_tuple']['ports']:
        name = Path(row['path']).name.removesuffix('.bin.gz')
        if name not in expected or name in seen:
            raise SystemExit('Invalid or repeated coefficient port in INSTANCE.json.')
        seen.add(name)
        inherited = expected[name]
        port = {'K': 'K0', 'MF_source': 'MF'}.get(name, name)
        packed = (ROOT / row['path']).read_bytes()
        raw = gzip.decompress(packed)
        if (row['polynomial_port'] != port
                or row['uncompressed_sha256'] != inherited['sha256']
                or row['gzip_sha256'] != inherited['gzip_sha256']
                or hashlib.sha256(raw).hexdigest() != row['uncompressed_sha256']
                or hashlib.sha256(packed).hexdigest() != row['gzip_sha256']):
            raise SystemExit('The active tuple does not match INSTANCE.json: ' + name)
    if seen != {'beta', 'K', 'MC', 'MF_source'}:
        raise SystemExit('INSTANCE.json must activate the complete four-port tuple.')
    parent = instance['parent']
    if hashlib.sha256((ROOT / parent['path']).read_bytes()).hexdigest() != parent['sha256']:
        raise SystemExit('The active parent does not match INSTANCE.json.')
    return instance


def main():
    if sys.version_info < (3, 10):
        raise SystemExit('Python 3.10 or newer is required.')
    if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):
        raise SystemExit('Run without -O or PYTHONOPTIMIZE: the audit uses assertions.')
    instance = verify_active_binding()
    GENERATED.mkdir(exist_ok=True)
    steps = [
        ('coefficient_rebuild', ['vendor/rebuild_coefficients.py'], None),
        ('build', ['build.py'], 'BUILD_RECEIPT.json'),
        ('independent_audit', ['checks/audit.py', '.'], None),
        ('source_interface', ['checks/source_interface.py', '--candidate', '.',
                              '--output', 'generated/SOURCE_INTERFACE_AUDIT.json'], None),
        ('sidon_and_toys', ['checks/sidon_and_toys.py', '--output',
                            'generated/SIDON_AND_TOYS_AUDIT.json'], None),
    ]
    summary = {'status': 'RUNNING', 'steps': [], 'active_binding_verified': True,
               'scope': 'Reproduction and arithmetic audits; no search for a Con(ZFC) solution.'}
    receipt = GENERATED / 'REPRODUCTION.json'
    for name, arguments, save_stdout in steps:
        command = [sys.executable, '-B', *arguments]
        result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
        record = {'name': name, 'command': ['python3', '-B', *arguments],
                  'exit_code': result.returncode,
                  'stdout_sha256': hashlib.sha256(result.stdout.encode()).hexdigest()}
        try:
            parsed = json.loads(result.stdout)
        except json.JSONDecodeError:
            parsed = None
        if save_stdout and parsed is not None:
            (GENERATED / save_stdout).write_text(json.dumps(parsed, indent=2) + '\n')
            record['receipt'] = 'generated/' + save_stdout
        summary['steps'].append(record)
        if result.returncode:
            summary['status'] = 'FAIL'
            record['stderr'] = result.stderr
            receipt.write_text(json.dumps(summary, indent=2) + '\n')
            if result.stdout:
                print(result.stdout, end='')
            if result.stderr:
                print(result.stderr, file=sys.stderr, end='')
            raise SystemExit(result.returncode)
        print(name + ': PASS')
    metrics = json.loads((GENERATED / 'METRICS.json').read_text())
    audit = json.loads((GENERATED / 'INDEPENDENT_AUDIT.json').read_text())
    if (metrics['total_operations'] != 809 or audit['exact_degree'] != 237520456
            or len(audit['variables']) != 10 or audit['status'] != 'PASS'
            or audit['variables'] != instance['polynomial']['variables']
            or audit['exact_degree'] != instance['polynomial']['exact_total_degree']
            or metrics['total_operations'] != instance['polynomial']['binary_arithmetic_operations']
            or metrics['source']['positions'] != instance['source_coding']['positions']):
        summary['status'] = 'FAIL'
        summary['error'] = 'Final metrics differ from the delivered instance.'
        receipt.write_text(json.dumps(summary, indent=2) + '\n')
        raise SystemExit(summary['error'])
    summary.update(status='PASS', unknown_domain='Z', unknowns=10,
                   exact_total_degree=audit['exact_degree'],
                   binary_arithmetic_operations=metrics['total_operations'],
                   receipts=['vendor/REBUILD_RECEIPT.json',
                             'generated/BUILD_RECEIPT.json',
                             'generated/INDEPENDENT_AUDIT.json',
                             'generated/SOURCE_INTERFACE_AUDIT.json',
                             'generated/SIDON_AND_TOYS_AUDIT.json'])
    receipt.write_text(json.dumps(summary, indent=2) + '\n')
    print('All checks passed: 10 integers; degree 237520456; 809 operations.')


if __name__ == '__main__':
    main()
