#!/usr/bin/env python3
"""Replay the delivered components in temporary copies; preserve sealed files."""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, help='Optional receipt path outside the sealed package')
    args = parser.parse_args()
    manifest = ROOT / 'MANIFEST.json'
    manifest_count = 0
    if manifest.exists():
        for entry in json.loads(manifest.read_text())['files']:
            data = (ROOT / entry['path']).read_bytes()
            require(len(data) == entry['bytes'], 'size mismatch: ' + entry['path'])
            require(hashlib.sha256(data).hexdigest() == entry['sha256'], 'hash mismatch: ' + entry['path'])
            manifest_count += 1
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    python = [sys.executable, '-B'] + (['-O'] if sys.flags.optimize else [])
    results = []
    with tempfile.TemporaryDirectory(prefix='con-zfc-replay-') as temporary:
        work = Path(temporary)
        for name in ('integer', 'direct', 'positive'):
            shutil.copytree(ROOT / name, work / name, ignore=shutil.ignore_patterns('__pycache__'))
        tasks = [
            ('integer-family', 'integer', ['verify.py']),
            ('integer-independent-norms', 'integer', ['independent_review/check.py']),
            ('direct-quartics', 'direct', ['verify.py']),
            ('positive-companions', 'positive', ['check.py']),
            ('compact44-coefficients', 'positive/coefficients/recipe', ['build_coefficients.py']),
        ]
        for label, directory, command in tasks:
            run = subprocess.run(python + command, cwd=work / directory, env=env,
                                 text=True, capture_output=True)
            require(run.returncode == 0,
                    label + ' failed\n' + run.stdout[-2500:] + '\n' + run.stderr[-2500:])
            results.append({'check': label, 'status': 'PASS',
                            'stdout_sha256': hashlib.sha256(run.stdout.encode()).hexdigest()})
        binding = json.loads((ROOT / 'positive/coefficients/BINDING.json').read_text())
        for port, entry in binding['ports'].items():
            packed = (ROOT / 'positive/coefficients' / entry['file']).read_bytes()
            raw = gzip.decompress(packed)
            require(hashlib.sha256(packed).hexdigest() == entry['sha256_gzip'], 'gzip hash ' + port)
            require(hashlib.sha256(raw).hexdigest() == entry['sha256_raw'], 'raw hash ' + port)
            require(len(raw) == entry['raw_bytes'], 'raw length ' + port)
            value = int.from_bytes(raw, 'little')
            require(value.bit_length() == entry['bits'], 'integer width ' + port)
            regenerated = work / 'positive/coefficients/recipe/coefficients' / (entry['upstream_port'] + '.bin.gz')
            require(gzip.decompress(regenerated.read_bytes()) == raw, 'coefficient regeneration ' + port)
        results.append({'check': 'positive-whole-tuple-binding', 'ports': 4, 'status': 'PASS'})
    receipt = {
        'status': 'PASS', 'python_optimized': bool(sys.flags.optimize),
        'manifest_files_checked': manifest_count, 'checks': results,
        'scope': 'Finite exact polynomial data, coefficient recipes, circuit counts, degree certificates, and deterministic rebuilds. The written proofs establish the new unbounded reductions; ordinary calibration theorems remain imported.'
    }
    data = json.dumps(receipt, indent=2) + '\n'
    if args.output:
        out = args.output.resolve()
        require(ROOT not in out.parents, 'Write the receipt outside the sealed package')
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(data)
    print(data, end='')


if __name__ == '__main__':
    main()
