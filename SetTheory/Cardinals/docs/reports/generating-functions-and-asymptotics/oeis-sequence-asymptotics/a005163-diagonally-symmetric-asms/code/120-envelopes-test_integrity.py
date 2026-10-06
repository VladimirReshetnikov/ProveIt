#!/usr/bin/env python3
"""Negative tests for the outer inventory, in fresh temporary directories."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

SCRIPT = Path(__file__).resolve().with_name('integrity.py')

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def run(root, mode, *args):
    return subprocess.run([sys.executable, '-B', *mode, str(SCRIPT), str(root), *args],
                          text=True, capture_output=True, timeout=30)

def main():
    mutations = [
        ('changed', 'HASH_MISMATCH'), ('missing', 'MISSING_FILE'),
        ('unexpected', 'UNEXPECTED_FILE'), ('symlink', 'SYMLINK'),
        ('duplicate', 'DUPLICATE_INVENTORY_PATH'), ('unsafe', 'UNSAFE_INVENTORY_PATH'),
        ('malformed', 'INVALID_INVENTORY_LINE'), ('unsorted', 'UNSORTED_INVENTORY'),
        ('empty', 'EMPTY_INVENTORY'), ('absent_manifest', 'MISSING_INVENTORY'),
        ('unexpected_directory', 'UNEXPECTED_DIRECTORY'),
        ('symlink_inventory', 'MISSING_INVENTORY'),
        ('symlink_directory', 'SYMLINK'),
        ('nested_inventory', 'UNEXPECTED_FILE'),
    ]
    for mode in ([], ['-O']):
        for name, diagnostic in mutations:
            with tempfile.TemporaryDirectory(prefix='report120-integrity-test-') as td:
                root=Path(td)
                (root/'a.txt').write_text('alpha\n')
                (root/'b.txt').write_text('beta\n')
                cp=run(root,mode,'--write')
                require(cp.returncode==0, 'SETUP_FAILED '+cp.stderr)
                manifest=root/'CHECKSUMS.sha256'
                original=manifest.read_text()
                if name=='changed': (root/'a.txt').write_text('ALPHA\n')
                elif name=='missing': (root/'a.txt').unlink()
                elif name=='unexpected': (root/'c.txt').write_text('gamma\n')
                elif name=='symlink': (root/'c.txt').symlink_to('a.txt')
                elif name=='duplicate': manifest.write_text(original+original.splitlines()[0]+'\n')
                elif name=='unsafe': manifest.write_text('0'*64+'  ../escape\n')
                elif name=='malformed': manifest.write_text('invalid\n')
                elif name=='unsorted': manifest.write_text('\n'.join(reversed(original.splitlines()))+'\n')
                elif name=='empty': manifest.write_text('')
                elif name=='absent_manifest': manifest.unlink()
                elif name=='unexpected_directory': (root/'empty').mkdir()
                elif name=='symlink_inventory':
                    manifest.unlink(); manifest.symlink_to('a.txt')
                elif name=='symlink_directory': (root/'linked').symlink_to('.', target_is_directory=True)
                elif name=='nested_inventory':
                    (root/'nested').mkdir(); (root/'nested'/'CHECKSUMS.sha256').write_text('extra\n')
                cp=run(root,mode)
                require(cp.returncode==1 and diagnostic in cp.stderr,
                        f'MUTATION_NOT_REJECTED {name} {mode}: {cp.returncode} {cp.stdout} {cp.stderr}')
    print(json.dumps({'status':'PASS','named_mutations':len(mutations),'modes':['normal','optimized'],
                      'negative_runs':2*len(mutations),'expected_diagnostics_verified':True},sort_keys=True))

if __name__=='__main__':
    main()
