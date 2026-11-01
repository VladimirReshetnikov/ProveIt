#!/usr/bin/env python3
"""Negative tests only: reject absent plan and aliased replay states."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

D = Path(__file__).resolve().parent
H = lambda path: hashlib.sha256(Path(path).read_bytes()).hexdigest()
names = ('prepare.py', 'replay.py', 'compare.py', 'run.py')
before = {name: H(D / name) for name in names}
self_hash = H(__file__)
for name in names:
    compile((D / name).read_text(), str(D / name), 'exec')
rows = []
with tempfile.TemporaryDirectory(prefix='ipra14-after107-comparator-negative-') as tmp:
    root = Path(tmp)
    x, y, z = root / 'x', root / 'y', root / 'z'
    for p in (x, y, z):
        p.mkdir()
    (x / 'state.json').write_text('{}')
    (y / 'state.json').write_text('{}')
    os.link(x / 'state.json', z / 'state.json')
    for name in ('compare.py', 'run.py'):
        for case, a, b in (('missing_plan', x, y), ('same_directory', x, x), ('same_state_inode', x, z)):
            w = root / (name.removesuffix('.py') + '-' + case)
            w.mkdir()
            for script in ('compare.py', 'run.py'):
                shutil.copyfile(D / script, w / script)
                assert H(w / script) == before[script]
            plan = root / 'missing-plan'
            parent = root / 'missing-parent-receipt'
            proc = subprocess.run([sys.executable, str(w / name), str(plan), str(a), str(b), str(parent)],
                                  capture_output=True, text=True)
            assert proc.returncode != 0 and not (w / 'receipt.json').exists() and not (w / 'terminal.json').exists(), (name, case, proc.returncode)
            if case == 'missing_plan':
                last = proc.stderr.splitlines()[-1]
                assert 'FileNotFoundError:' in last and str(plan / 'manifest.json') in last, (name, proc.stderr)
            else:
                assert 'author and peer must be independent runs' in proc.stderr, (name, case, proc.stderr)
            rows.append({'script': name, 'case': case, 'exit_code': proc.returncode,
                         'stdout': proc.stdout, 'stderr': proc.stderr})
assert {name: H(D / name) for name in names} == before and H(__file__) == self_hash
out = {'status': 'PASS_FAIL_CLOSED_NEGATIVE_CHECKS', 'files_sha256': before,
       'checker_sha256': self_hash, 'rows': rows,
       'scope': 'Both scripts were present in every isolated execution; syntax and absent-plan / identical-directory / shared-state-inode tests only. No replay or comparator pass.'}
path = D / 'comparator-negative-checks.json'
with path.open('x') as handle:
    json.dump(out, handle, indent=2, sort_keys=True)
    handle.write('\n')
print('PASS_FAIL_CLOSED_NEGATIVE_CHECKS', len(rows), H(path))
