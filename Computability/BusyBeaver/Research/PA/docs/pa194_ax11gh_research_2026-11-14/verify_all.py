#!/usr/bin/env python3
"""Offline replay of both new constructions and their finite certificates.

Full mode reruns the independent literal proofs. Quick mode checks retained
certificates and reruns the inexpensive checks, and records its omissions.
Neither mode claims a proof-assistant derivation of the arithmetic theorem.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent
NAMES = ('PA194AX11GH', 'PA194AX11GHS')


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def run(output, tag, args):
    logfile = output / (tag + '.log')
    started = time.monotonic()
    with logfile.open('w') as log:
        result = subprocess.run([sys.executable, '-B'] + list(map(str, args)),
                                cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        print(logfile.read_text()[-12000:])
        raise RuntimeError(f'{tag} failed with exit {result.returncode}; see {logfile}')
    receipt = dict(check=tag, status='PASS', seconds=round(time.monotonic()-started, 3))
    print(tag + ': PASS', flush=True)
    return receipt


def main():
    assert __debug__ and not sys.flags.optimize, 'Run without -O.'
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    output = args.output or Path(tempfile.mkdtemp(prefix='pa194-ax11gh-verify-'))
    output.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    manifest = ROOT / 'SHA256SUMS'
    integrity = 0
    if manifest.exists():
        for line in manifest.read_text().splitlines():
            digest, relative = line.split('  ', 1)
            assert sha(ROOT / relative) == digest, relative
            integrity += 1
    checks = []
    build_args = [ROOT/'construction/build.py', '--output', output/'construction']
    if args.quick:
        build_args += ['--quick']
    checks.append(run(output, 'construction', build_args))
    for name, variant in zip(NAMES, ('gh', 'ghs')):
        machine = ROOT/'machines'/name
        checks.append(run(output, name+'-source', [ROOT/'verification/check_source.py',
            '--machine', machine, '--variant', variant, '--output', output/(name+'-source')]))
        checks.append(run(output, name+'-commands', [ROOT/'verification/check_commands.py',
            '--machine', machine, '--output', output/(name+'-commands.json')]))
    if not args.quick:
        checks.append(run(output, 'literal', [ROOT/'verification/independent/check.py',
                                             '--output', output/'literal']))
        for name in NAMES:
            for filename in ('contracts.json', 'list_lemmas.json', 'startup.json'):
                assert ((output/'literal'/name/filename).read_bytes() ==
                    (ROOT/'verification/independent/recorded'/name/filename).read_bytes()), (name, filename)
    checks.append(run(output, 'physical-frame-closure', [ROOT/'verification/physical_audit.py',
        '--bundle', ROOT, '--output', output/'physical_audit.json']))
    checks.append(run(output, 'comparison', [ROOT/'comparison/verify_bundle.py',
                                            '--receipt', output/'comparison.json']))
    summary = dict(status='PASS', mode='quick' if args.quick else 'full',
                   file_hashes_checked=integrity, checks=checks,
                   full_literal_replay=not args.quick,
                   full_construction_runtime_replay=not args.quick,
                   retained_literal_certificates_bound=True,
                   fresh_literal_bytes_equal_retained=None if args.quick else True,
                   kernel_checked=False, arithmetic_derivation_checked_by_this_script=False,
                   inherited_calibration='Updated incoming PA194QAX11H written manuscript; '
                     'the report states the dependency separately from these finite checks.',
                   seconds=round(time.monotonic()-started,3))
    (output/'summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    print(json.dumps(summary, indent=2))
    print('output:', output)


if __name__ == '__main__':
    main()
