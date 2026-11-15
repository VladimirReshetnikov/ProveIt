#!/usr/bin/env python3
"""Rebuild and verify PA194GS offline, preserving the delivered receipts.

Default: full independent literal replay plus the fast checks.
--quick: validate saved certificate bindings, source identity, complete blank
startup, contextual folds, graph novelty, and a deterministic reconstruction;
skip only the expensive universal literal replay.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
import time

ROOT=Path(__file__).resolve().parent


def run(*args):
    subprocess.run([sys.executable,'-B',*[str(a) for a in args]],
                   check=True,cwd=ROOT)


def verify(quick, output):
    assert __debug__, 'Run without -O'
    began=time.monotonic()
    manifest=ROOT/'SHA256SUMS'
    files=0
    if manifest.exists():
        for line in manifest.read_text().splitlines():
            expected,name=line.split('  ',1)
            path=ROOT/name
            assert path.is_file(), name
            assert hashlib.sha256(path.read_bytes()).hexdigest()==expected, name
            files+=1
    with tempfile.TemporaryDirectory(prefix='pa194gs-') as directory:
        work=Path(directory)
        candidate=work/'candidate'
        run(ROOT/'build.py','--output',candidate)
        compared=['machine.tm','machine.native.tm','raw.native.tm','labels.json',
                  'sites.json','instructions.json','nodes.json','tree.json',
                  'folds.json','local_folds.json']
        for name in compared:
            assert (candidate/name).read_bytes()==(ROOT/'machine'/name).read_bytes(), name
        run(ROOT/'verification/check_source.py','--candidate',candidate,
            '--output',work/'source.json')
        run(ROOT/'verification/check_startup.py','--candidate',candidate,
            '--output',work/'startup.json')
        run(ROOT/'verification/check_clocks.py','--output',work/'saved_clocks.json')
        run(ROOT/'verification/check_linear_clocks.py','--output',work/'linear_clocks.json')
        run(ROOT/'verification/check_novelty.py','--output',work/'novelty.json')
        if not quick:
            run(ROOT/'verification/check_literal.py',candidate)
            assert (candidate/'independent/contracts.json').read_bytes()==(
                ROOT/'machine/independent/contracts.json').read_bytes()
            run(ROOT/'verification/check_clocks.py','--candidate',candidate,
                '--output',work/'fresh_clocks.json')
    result=dict(status='PASS',mode='quick' if quick else 'full',
                manifest_files=files,reconstructed_files=len(compared),
                full_literal_replay=not quick,
                saved_certificate_bindings=True,source_identity=True,
                sparse_complete_startup=True,novelty=True,linear_clock_audit=True,
                elapsed_seconds=round(time.monotonic()-began,3),
                scope='Finite machine/source/certificate checks; not a Lean kernel or the complete PA proof compiler.')
    if output:
        output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--quick',action='store_true')
    p.add_argument('--output',type=Path)
    a=p.parse_args()
    verify(a.quick,a.output)
