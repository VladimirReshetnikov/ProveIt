#!/usr/bin/env python3
"""Reproduce the shared implication core and both maintained Lean adapters.

The six-goal derivation, renderer, and Lukasiewicz adapter originate at
49e99c5b7cc6c2e164331961de28bad3904361fd.  This wrapper reconciles that existing
work with the maintained --out/--check interface at 57541fe0cfe3.  Its hashes
are provenance and regeneration checks; Lean's kernel checks the proofs.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
DEFAULT_OUT = (HERE / '../../../Lean').resolve()
INPUT_PINS = {
    'rho8cd/generate_domrho8_cd.py': '63da860d3a957010c53d783a2b8995acef3d8e3806823f24fc5833738dc1d56a',
    'rho8cd/derivation_core.txt': '4141248ed90a6813c07f274351336963acde1d82f6ea463a33e5f7d64bed8005',
    'dominated_implication_templates/adapter.txt': '8fdbec0db9134070bee2dfa0a433aff66ab83c00007ea7b9aabd9192c506d378',
    'dominated_implication_templates/lukasiewicz.txt': '7d443a733b5c5ddd0d49728cf1ea7d855dd445f156934c13578bacc008c59874',
}
OUTPUT_PINS = {
    'DominatedImplication.lean': 'bd07364a829e8a1535b0ecf1ee6ed0c292d5af35e01a6db8f152dd2610e247d8',
    'DomRho8.lean': '8fdbec0db9134070bee2dfa0a433aff66ab83c00007ea7b9aabd9192c506d378',
    'Lukasiewicz.lean': '7d443a733b5c5ddd0d49728cf1ea7d855dd445f156934c13578bacc008c59874',
}

def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def generate() -> tuple[dict[str, bytes], dict]:
    if not __debug__:
        raise RuntimeError('Use ordinary Python without -O')
    inputs = {}
    for name, expected in INPUT_PINS.items():
        data = (HERE / name).read_bytes()
        if sha(data) != expected:
            raise ValueError('Pinned input changed: ' + name)
        inputs[name] = data
    with tempfile.TemporaryDirectory(prefix='shared-implication-') as tmp:
        core = Path(tmp) / 'DominatedImplication.lean'
        subprocess.run([
            sys.executable, '-B', str(HERE / 'rho8cd/generate_domrho8_cd.py'),
            '--derivation', str(HERE / 'rho8cd/derivation_core.txt'),
            '--core', str(core),
        ], check=True)
        outputs = {
            'DominatedImplication.lean': core.read_bytes(),
            'DomRho8.lean': inputs['dominated_implication_templates/adapter.txt'],
            'Lukasiewicz.lean': inputs['dominated_implication_templates/lukasiewicz.txt'],
        }
    for name, data in outputs.items():
        if sha(data) != OUTPUT_PINS[name]:
            raise ValueError('Generated output differs: ' + name)
    metrics = {
        'input_sha256': INPUT_PINS,
        'outputs': {name: {'sha256': sha(data), 'bytes': len(data),
                          'lines': len(data.splitlines())}
                    for name, data in outputs.items()},
        'proof_origin_commit': '49e99c5b7cc6c2e164331961de28bad3904361fd',
        'status': 'Byte reproduction only; see separate Lean kernel receipts.',
    }
    return outputs, metrics

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, help='Lean source root for output')
    parser.add_argument('--check', action='store_true', help='compare exact output bytes')
    args = parser.parse_args()
    outputs, metrics = generate()
    target = (args.out or DEFAULT_OUT) / 'BusyBeaver/ZFC'
    if args.check or args.out is None:
        for name, data in outputs.items():
            if (target / name).read_bytes() != data:
                raise ValueError('Maintained source differs: ' + name)
    else:
        target.mkdir(parents=True, exist_ok=True)
        for name, data in outputs.items():
            (target / name).write_bytes(data)
        (args.out / 'metrics.json').write_text(json.dumps(metrics, indent=2) + '\n')
    print(json.dumps(metrics, indent=2))

if __name__ == '__main__':
    main()
