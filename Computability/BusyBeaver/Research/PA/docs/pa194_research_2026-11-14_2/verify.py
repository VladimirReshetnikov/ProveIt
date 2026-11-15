#!/usr/bin/env python3
"""Verify the packaged identities and replay both new constructions.

Default: portable quick checks; --full: also rerun all symbolic tape
outcomes; --novelty: additionally repeat exact corpus novelty comparisons.
The completed full evidence is already included. No mode kernel-checks
the mathematical consistency proof or reruns the research searches.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent

def main():
    assert __debug__ and not sys.flags.optimize, 'Run without Python -O.'
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--full', action='store_true')
    parser.add_argument('--novelty', action='store_true')
    parser.add_argument('--output', type=Path, default=Path.cwd()/'fresh_verification.json')
    args = parser.parse_args()
    checked = 0
    for line in (ROOT/'SHA256SUMS').read_text().splitlines():
        digest, relative = line.split('  ', 1)
        assert hashlib.sha256((ROOT/relative).read_bytes()).hexdigest() == digest, relative
        checked += 1
    print(f'Packaged SHA-256 identities: PASS ({checked} files)', flush=True)
    with tempfile.TemporaryDirectory(prefix='pa194-delivery-') as temporary:
        temp = Path(temporary)
        receipts = {}
        def run(label, command):
            log_path = temp/(label+'.log')
            with log_path.open('w') as log:
                result = subprocess.run([sys.executable, '-B', *map(str, command)],
                                        cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
            if result.returncode:
                print(log_path.read_text(), file=sys.stderr)
                raise RuntimeError(label+' failed')
            print(label+': PASS', flush=True)
        for candidate in ['AX11QGH', 'AX11HR']:
            receipt = temp/(candidate+'.json')
            command = [ROOT/'construction'/candidate/'verify_all.py', '--receipt', receipt]
            if not args.full:
                command.append('--quick')
            run(candidate, command)
            receipts[candidate] = json.loads(receipt.read_text())
            if args.novelty:
                novelty = temp/(candidate+'_novelty.json')
                run(candidate+'_novelty', [ROOT/'comparison/verify_novelty.py',
                    ROOT/'construction'/candidate/'machine/machine.tm', '--output', novelty])
                receipts[candidate]['novelty'] = json.loads(novelty.read_text())
        result = dict(status='PASS', files_hashed=checked, full_literal_replay=args.full,
                      novelty_replayed=args.novelty, research_searches_replayed=False,
                      candidates=receipts, kernel_checked=False)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2)+'\n')
        print('Fresh receipt: '+str(args.output.resolve()), flush=True)

if __name__ == '__main__':
    main()
