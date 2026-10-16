#!/usr/bin/env python3
"""Reproduce the frozen public253 state-fusion experiments offline.

Default: all checks, including the approximately four-minute affine search.
--quick: local searches and controls only. Outputs go in this directory.
--repo PATH: restage exact inputs from a local ProveIt checkout first.
Only Python's standard library is required. No external code is executed
except the clearly attributed, hash-pinned Python source snapshots.
"""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import shutil
import subprocess
import sys

HERE=Path(__file__).resolve().parent
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--quick',action='store_true')
    ap.add_argument('--repo',type=Path)
    args=ap.parse_args()
    if not __debug__: raise SystemExit('Run without -O/-OO; assertions enforce the experimental contracts.')
    manifest=json.loads((HERE/'source_manifest.json').read_text())
    for name,item in manifest['files'].items():
        target=HERE/'source'/name
        if args.repo:
            original=args.repo/item['repository_path']
            if not original.is_file(): raise SystemExit(f'Missing source snapshot: {original}')
            target.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(original,target)
        digest=hashlib.sha256(target.read_bytes()).hexdigest()
        if digest!=item['sha256']: raise SystemExit(f'Source bytes differ from the frozen pin: {name}')
    def run(*arguments):
        subprocess.run([sys.executable,*map(str,arguments)],cwd=HERE,check=True)
    for radius,bound in [(4,64),(6,128)]:
        run('source/audit_tm.py','source/zfc_253.tm',
            '--expected-sha256',manifest['files']['zfc_253.tm']['sha256'],
            '--expected-states',253,'--expected-halt',253,
            '--source-commit','0d544f2a2e3c18f12278441a74b7879f31cbe856',
            '--window-radius',radius,'--macro-steps',bound,'--self-test',
            '--output',f'public253-window{radius}-audit.json')
        result=json.loads((HERE/f'public253-window{radius}-audit.json').read_text())
        local=result['local_window_macro_search']
        assert local['ordered_state_pairs_checked']==63756
        assert not local['safe_single_state_merges']
    run('hybrid_window_search.py')
    mixed=json.loads((HERE/'hybrid-window-results.json').read_text())
    assert len(mixed['candidates'])==50086 and not mixed['safe_fusions']
    assert mixed['abstract_configurations']==335369 and mixed['total_windows_tested']==111311
    run('check_controls.py')
    if not args.quick:
        run('hybrid_fusion_search.py')
        affine=json.loads((HERE/'hybrid-fusion-results.json').read_text())
        assert len(affine['candidates'])==50086 and not affine['runtime_survivors']
        assert sum(c['tested']for c in affine['candidates'])==489647
        assert affine['failure_reason_counts']['fuel']==45443
    print('PASS: frozen-input experiment counts and controls reproduced.'+
          (' Affine family search omitted by --quick.'if args.quick else ''))

if __name__=='__main__': main()
