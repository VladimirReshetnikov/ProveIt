#!/usr/bin/env python3
"""Check the changed frozen header with Lean's dependency parser only."""
import hashlib
import json
import os
from pathlib import Path
import subprocess

D = Path(__file__).resolve().parent
M = D / 'manifest.json'
P = Path('/tmp/ipra-current-repaired-build-y6kamkla')
L = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PKG = Path('/tmp/pra14-full-transitive-2x6o__to/package-lib')
TOOL = L.parent.parent / 'lib/lean'
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
inputs = [Path(__file__).resolve(), M, P / 'state.json', L]
before = {str(p): H(p) for p in inputs}
m = json.loads(M.read_text())
assert m['seed'] == 'ZFCinPA.SeparationKernel' and json.loads((P / 'state.json').read_text())['status'] == 'PASS'
src = D / 'sources' / (m['seed'].replace('.', '/') + '.lean')
assert src.is_file() and not src.is_symlink() and H(src) == m['sources'][m['seed']]['sha256']
env = dict(os.environ, LEAN_PATH=str(P / 'lib') + ':' + str(PKG))
env.pop('LEAN_SRC_PATH', None)
proc = subprocess.run([str(L), '--deps', str(src)], env=env, capture_output=True, text=True)
assert proc.returncode == 0, (proc.stderr, proc.stdout)
actual = set()
for line in proc.stdout.splitlines():
    p = Path(line)
    rel = next((p.relative_to(root) for root in (P / 'lib', PKG, TOOL) if p.is_relative_to(root)), None)
    assert rel is not None and str(rel).endswith('.olean'), line
    actual.add(str(rel)[:-len('.olean')].replace('/', '.'))
expected = set(m['sources'][m['seed']]['imports']) - {'Init'}
assert actual - {'Init'} == expected, (expected, actual)
assert {str(p): H(p) for p in inputs} == before and H(src) == m['sources'][m['seed']]['sha256']
out = D / 'lean-deps-receipt.json'
assert not out.exists(), 'refusing to overwrite earlier evidence'
out.write_text(json.dumps({'status': 'PASS_HEADER_DEPS', 'input_sha256': before,
                           'module': m['seed'], 'stdout': proc.stdout,
                           'stdout_sha256': hashlib.sha256(proc.stdout.encode()).hexdigest(),
                           'scope': 'Source dependency parsing only; the historical resolver is not a current proof.'},
                          indent=2, sort_keys=True) + '\n')
print('PASS_HEADER_DEPS', m['seed'], H(out))
