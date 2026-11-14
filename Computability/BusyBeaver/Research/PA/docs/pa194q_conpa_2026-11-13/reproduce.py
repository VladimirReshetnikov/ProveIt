#!/usr/bin/env python3
"""Rebuild and verify the delivered PA194Q, optionally also PA194CSZ."""
from pathlib import Path
import argparse
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
if not __debug__:
    raise RuntimeError('Certificate assertions must be enabled; do not use -O.')
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--secondary', action='store_true', help='also verify PA194CSZ')
parser.add_argument('--quick', action='store_true',
                    help='skip independent literal replays; retain construction checks')
args = parser.parse_args()

def run(relative, *extra):
    print('\nRunning ' + relative, flush=True)
    subprocess.run([sys.executable, '-B', str(ROOT / relative), *extra],
                   cwd=ROOT, check=True)

run('construction/build.py')
run('verification/exchange_certificate.py')
run('verification/check_logic.py')
run('comparison/check_novelty.py', 'machine/pa194q.tm',
    '--output', 'evidence/novelty.json')
novelty = json.loads((ROOT / 'evidence/novelty.json').read_text())
assert novelty['graph_novel_under_state_renaming_start_choice_reflection_and_symbol_complement']
if not args.quick:
    run('verification/check.py')
if args.secondary:
    if args.quick:
        run('secondary/pa194csz/build_csz.py')
        run('secondary/pa194csz/check_invariant.py')
    else:
        run('secondary/pa194csz/verify.py')
print('\nPASS: PA194Q' + (' and PA194CSZ' if args.secondary else '')
      + (' (independent literal replays skipped by --quick)' if args.quick
         else ' with independent literal-tape replay'), flush=True)
