#!/usr/bin/env python3
"""Replay the recorded experiments using their exact source versions in a copy."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--experiment', choices=('baseline', 'compressed'), required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=7)
    parser.add_argument('--scope', choices=('all', 'actual', 'kernel'), default='all')
    parser.add_argument('--sample-seconds', type=float, default=0.02)
    parser.add_argument('--scan-seconds', type=float, default=30)
    parser.add_argument('--prepare-only', action='store_true',
                        help='verify copied source hashes without rerunning timings')
    args = parser.parse_args()
    if sys.flags.optimize:
        parser.error('benchmark verification requires assertions; run without -O or PYTHONOPTIMIZE')
    output = args.output.resolve()
    if output.exists():
        parser.error('output already exists; choose a new name to retain the previous measurements')
    names = {
        'baseline': ('benchmark_corridor.py', 'corridor_benchmark_20261008.json'),
        'compressed': ('benchmark_compressed_corridor.py', 'compressed_corridor_20261008.json'),
    }
    driver, record_name = names[args.experiment]
    recorded = json.loads((ROOT / 'fast/results' / record_name).read_text())
    with tempfile.TemporaryDirectory(prefix='unknot-kernels-benchmark-') as directory:
        tmp = Path(directory)
        for name in ('fast', 'reference'):
            shutil.copytree(ROOT / name, tmp / name,
                            ignore=shutil.ignore_patterns('__pycache__', '.pytest_cache'))
        if args.experiment == 'baseline':
            shutil.copyfile(tmp / 'reference/corridor_v1.py', tmp / 'fast/fastunknot/corridor.py')
        hashes = {'driver': hashlib.sha256((tmp / 'fast' / driver).read_bytes()).hexdigest()}
        assert hashes['driver'] == recorded['benchmark_sha256']
        for name, expected in recorded['implementation_sha256'].items():
            hashes[name] = hashlib.sha256((tmp / 'fast/fastunknot' / name).read_bytes()).hexdigest()
            assert hashes[name] == expected, (name, hashes[name], expected)
        reference_key, reference_name = (
            ('prior_sha256', 'graded_transfer_v1.py') if args.experiment == 'baseline'
            else ('frozen_sha256', 'corridor_v1.py'))
        assert hashlib.sha256((tmp / 'reference' / reference_name).read_bytes()).hexdigest() == recorded[reference_key]
        print(json.dumps({'experiment': args.experiment, 'verified_source_hashes': hashes}, indent=2), flush=True)
        if args.prepare_only:
            return
        output.parent.mkdir(parents=True, exist_ok=True)
        command = [sys.executable, driver, '--output', str(output), '--rounds', str(args.rounds),
                   '--scope', args.scope, '--sample-seconds', str(args.sample_seconds),
                   '--scan-seconds', str(args.scan_seconds)]
        subprocess.run(command, cwd=tmp / 'fast', check=True)


if __name__ == '__main__':
    main()
