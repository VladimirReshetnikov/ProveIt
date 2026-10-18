#!/usr/bin/env python3
"""Run the complete portable Prefix246 verification suite, without network access."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]

def main():
    if not __debug__: raise SystemExit('Assertions required; run without -O.')
    commands = [
        ['code/rebuild_machines.py','--check'],
        ['code/check_folds.py'],
        ['code/render_table.py','--check'],
        ['code/check_macro_inductions.py'],
        ['code/review_affine_source.py',
         '--program','sources/Prog254.v',
         '--sites','sources/prior/instruction-sites-physical.json',
         '--table','machine/zfc_prefix246_old.tm',
         '--checker','sources/prior/prefix_affine.py',
         '--output','results/affine-source-review.json'],
        ['code/check_bootstrap.py'],
        ['code/check_literal_instructions.py',
         '--program','sources/Prog254.v',
         '--table','machine/zfc_prefix246_old.tm',
         '--output','results/literal-instructions.json'],
        ['code/check_local_contracts.py'],
        ['code/check_prefix_boxes.py'],
    ]
    records = []
    began = time.monotonic()
    for command in commands:
        start = time.monotonic()
        result = subprocess.run([sys.executable,'-B',*command], cwd=ROOT,
            text=True, capture_output=True)
        print(' '.join(command), 'PASS' if result.returncode == 0 else 'FAIL', flush=True)
        if result.returncode:
            print(result.stdout)
            print(result.stderr, file=sys.stderr)
            raise SystemExit(result.returncode)
        records.append(dict(command=[sys.executable,'-B',*command],
            returncode=result.returncode, seconds=time.monotonic()-start,
            stdout=result.stdout, stderr=result.stderr))
    summary = dict(status='PASS', seconds=time.monotonic()-began, commands=records,
        python=sys.version, scope='Finite computational proof checks and literal audits; '
            'the symbolic induction rules are reviewed mathematics, not a Lean/Rocq kernel.')
    (ROOT/'results/verification-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print('ALL PREFIX246 CHECKS PASS', flush=True)

if __name__ == '__main__': main()
