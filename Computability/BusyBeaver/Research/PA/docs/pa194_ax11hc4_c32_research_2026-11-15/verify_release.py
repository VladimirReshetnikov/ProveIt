#!/usr/bin/env python3
"""Portable verification entry point; Python 3.10+ and Node.js 18+."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent

def run(args, cwd=ROOT):
    print('+ ' + ' '.join(map(str, args)), flush=True)
    subprocess.run(list(map(str, args)), cwd=cwd, check=True)

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--literal', action='store_true', help='rederive literal list lemmas and all positive affine clocks')
    p.add_argument('--novelty', action='store_true', help='recheck all 526 corpus classes and the candidate pair')
    args = p.parse_args()
    if not __debug__ or sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE'):
        raise RuntimeError('Run with assertions enabled; remove PYTHONOPTIMIZE.')
    sums = ROOT / 'SHA256SUMS'
    if sums.exists():
        checked = 0
        for line in sums.read_text().splitlines():
            expected, relative = line.split('  ', 1)
            path = ROOT / relative
            actual = hashlib.sha256(path.read_bytes()).hexdigest()
            if actual != expected:
                raise RuntimeError('Release hash mismatch: ' + relative)
            checked += 1
        print('Release file hashes verified:', checked, flush=True)
    else:
        print('Development tree: no SHA256SUMS yet.', flush=True)
    node = shutil.which('node')
    if not node:
        raise RuntimeError('Node.js is required for the independent JavaScript replay.')
    con = ROOT / 'construction'
    py = [sys.executable, '-B']
    with tempfile.TemporaryDirectory(prefix='pa194_release_') as td:
        out = Path(td)
        for family, script, stem, supplied in [
            ('C32', con/'reconstruct.py', 'pa194_c32', con/'cycle32/pa194_cycle32'),
            ('HC4', con/'ax11hc4/reconstruct.py', 'pa194_ax11hc4', con/'ax11hc4/machine/pa194_ax11hc4'),
        ]:
            dest = out / family
            run(py + [script, '--output', dest])
            for suffix in ('.tm', '.native.tm'):
                if (dest/(stem+suffix)).read_bytes() != Path(str(supplied)+suffix).read_bytes():
                    raise RuntimeError('Reconstructed table mismatch: ' + family + suffix)
        for base in (con, con/'ax11hc4'):
            run(py + [base/'verify_source.py'])
            run([node, base/'verify_source.cjs'])
        if args.literal:
            for family in ('C32', 'HC4'):
                run(py + [con/'verify_literal.py', family])
        if args.novelty:
            receipt = out/'novelty.json'
            run(py + [ROOT/'comparison/novelty.py',
                      con/'ax11hc4/machine/pa194_ax11hc4.tm',
                      con/'cycle32/pa194_cycle32.tm', '--output', receipt])
            data = json.loads(receipt.read_text())
            assert all(c['spanning_classes'] == 526 and not c['matches']
                       and c['positive_orientation_controls'] == 4
                       for c in data['candidates'])
            assert all(c['distinct'] for c in data['pairwise'])
    print('PASS: all requested release checks completed.', flush=True)

if __name__ == '__main__':
    main()
