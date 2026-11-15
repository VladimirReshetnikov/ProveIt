#!/usr/bin/env python3
"""Reconstruct PA194AX11HR and replay its exact portable certificates.

Default mode repeats all literal source outcomes. --quick checks the
reconstruction, startup, recorded endpoint closure and positive durations,
but explicitly skips the expensive independent per-site literal replay.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
DENSE_SHA = 'b3c07bf7a750e1e9529929ef392fc0543645ccc34a7a39c3360ec41201f0e980'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    assert __debug__ and not sys.flags.optimize, 'Run without Python -O.'
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick', action='store_true')
    parser.add_argument('--receipt', type=Path, default=ROOT/'evidence/replay_receipt.json')
    args = parser.parse_args()
    for name, digest in json.loads((ROOT/'INPUT_SHA256.json').read_text()).items():
        assert sha(ROOT/name) == digest, name
    assert sha(ROOT/'machine/machine.tm') == DENSE_SHA
    with tempfile.TemporaryDirectory(prefix='pa194ax11hr-') as name:
        temp = Path(name)
        def run(label, command):
            log_path = temp/(label+'.log')
            with log_path.open('w') as log:
                result = subprocess.run([sys.executable, '-B', *map(str, command)],
                                        cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
            if result.returncode:
                print(log_path.read_text(), file=sys.stderr)
                raise RuntimeError(label+' failed')
            print(label+': PASS', flush=True)
        run('reconstruction', [ROOT/'build.py', '--output', temp/'machine'])
        for name in ['machine.tm', 'machine.native.tm', 'labels.json',
                     'sites.json', 'instructions.json', 'receipt.json']:
            assert (temp/'machine'/name).read_bytes() == (ROOT/'machine'/name).read_bytes(), name
        independent = None
        if not args.quick:
            run('independent_literal', [ROOT/'verification/check_literal.py',
                                       '--machine', temp/'machine',
                                       '--output', temp/'independent'])
            for name in ['contracts.json', 'list_lemmas.json', 'receipt.json']:
                assert (temp/'independent'/name).read_bytes() == (ROOT/'machine/independent'/name).read_bytes(), name
            independent = json.loads((temp/'independent/receipt.json').read_text())
        run('frame_closure', [ROOT/'verification/audit_closure.py',
                              '--bundle', ROOT, '--output', temp/'closure.json'])
        closure = json.loads((temp/'closure.json').read_text())
        assert closure['status'] == 'PASS'
        receipt = dict(status='PASS', family='PA194AX11HR', working_states=194,
                       dense_sha256=DENSE_SHA, startup_steps=48320,
                       reconstruction='PASS', physical_frame_closure=closure,
                       independent_literal_replay=independent,
                       quick_mode=args.quick, per_site_literal_replay_skipped=args.quick,
                       kernel_checked=False)
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(json.dumps(receipt, indent=2)+'\n')
        print(json.dumps(receipt, indent=2))

if __name__ == '__main__':
    main()
