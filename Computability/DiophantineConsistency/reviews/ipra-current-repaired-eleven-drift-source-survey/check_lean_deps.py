#!/usr/bin/env python3
"""Check the three newest frozen headers with Lean's dependency parser only."""
import hashlib
import json
import os
from pathlib import Path
import subprocess

D = Path(__file__).resolve().parent
M = D / 'manifest.json'
P = Path('/tmp/ipra-six-drift-replay-42b7hj5k')
L = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PKG = Path('/tmp/pra14-full-transitive-2x6o__to/package-lib')
TOOL = L.parent.parent / 'lib/lean'
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
inputs = [Path(__file__).resolve(), M, P / 'state.json', L]
before = {str(p): H(p) for p in inputs}
m = json.loads(M.read_text())
names = {'DiophantineConsistency.PRAWitnessCalculus',
         'DiophantineConsistency.PRAWitnessFormulaFunctions', 'ZFCinPA.SetCongruence'}
assert names <= set(m['seeds']) and json.loads((P / 'state.json').read_text())['status'] == 'PASS'
env = dict(os.environ, LEAN_PATH=str(P / 'lib') + ':' + str(PKG))
env.pop('LEAN_SRC_PATH', None)
rows = {}
for name in sorted(names):
    path = D / 'sources' / (name.replace('.', '/') + '.lean')
    assert path.is_file() and not path.is_symlink() and H(path) == m['sources'][name]['sha256']
    proc = subprocess.run([str(L), '--deps', str(path)], env=env, capture_output=True, text=True)
    assert proc.returncode == 0, (name, proc.stderr, proc.stdout)
    actual = set()
    for line in proc.stdout.splitlines():
        p = Path(line)
        rel = next((p.relative_to(root) for root in (P / 'lib', PKG, TOOL) if p.is_relative_to(root)), None)
        assert rel is not None and str(rel).endswith('.olean'), (name, line)
        actual.add(str(rel)[:-len('.olean')].replace('/', '.'))
    expected = set(m['sources'][name]['imports']) - {'Init'}
    assert actual - {'Init'} == expected, (name, expected, actual)
    rows[name] = {'stdout': proc.stdout, 'stdout_sha256': hashlib.sha256(proc.stdout.encode()).hexdigest(),
                  'count': len(expected)}
assert {str(p): H(p) for p in inputs} == before
assert all(H(D / 'sources' / (n.replace('.', '/') + '.lean')) == m['sources'][n]['sha256'] for n in rows)
out = D / 'lean-deps-receipt.json'
assert not out.exists(), 'refusing to overwrite earlier evidence'
out.write_text(json.dumps({'status': 'PASS_HEADER_DEPS', 'input_sha256': before, 'rows': rows,
                           'scope': 'Source dependency parsing only; the historical resolver is not a current proof.'},
                          indent=2, sort_keys=True) + '\n')
print('PASS_HEADER_DEPS', len(rows), H(out))
