#!/usr/bin/env python3
"""Reproduce the GH table and both symbolic checks using only Python stdlib."""
import hashlib
import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def run(*args):
    subprocess.run([sys.executable, '-B', *map(str, args)], cwd=ROOT, check=True)


def main(receipt_output=None):
    assert __debug__ and not sys.flags.optimize, 'Do not use Python -O.'
    with tempfile.TemporaryDirectory(prefix='pa194gh-verify-') as td:
        output = Path(td)
        run(ROOT / 'build.py', '--output', output / 'machine')
        names = ['machine.tm', 'machine.native.tm', 'raw.native.tm', 'labels.json',
                 'sites.json', 'instructions.json', 'nodes.json', 'folds.json',
                 'local_folds.json', 'startup.json', 'receipt.json']
        for name in names:
            assert (output / 'machine' / name).read_bytes() == (ROOT / 'machine' / name).read_bytes(), name
        run(ROOT / 'check_source_relation.py', '--output', output / 'source_relation.json')
        run(ROOT / 'check_commands.py', '--output', output / 'commands.json')
        run(ROOT / 'independent/check.py', output / 'machine', '--output', output / 'independent')
        independent = json.loads((output / 'independent/PA194GH/receipt.json').read_text())
        assert independent == json.loads((ROOT / 'independent/results/PA194GH/receipt.json').read_text())
        result = {
            'status': 'PASS', 'reproduced_artifacts': names,
            'dense_sha256': hashlib.sha256((output / 'machine/machine.tm').read_bytes()).hexdigest(),
            'independent_receipt_reproduced': True,
            'absolute_ipra_calibration': False, 'kernel_checked': False
        }
    if receipt_output is not None:
        receipt_output.parent.mkdir(parents=True, exist_ok=True)
        receipt_output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Write a fresh replay receipt here; by default only print it.')
    args = parser.parse_args()
    main(args.output)
