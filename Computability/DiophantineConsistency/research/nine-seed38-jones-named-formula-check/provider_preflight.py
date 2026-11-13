#!/usr/bin/env python3
"""Recheck the exact endpoint, Jones evaluator and seed producers; no Lean."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
P = Path(__file__).resolve().parent
D = P.parents[1]
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()

audits = (
    ('nine-sharing-norm38-ipra-endpoint-terminal-frontier-independent',
     '724290f08a1e7a6b992e4f947c72536a66fe87bc59b0c6aaeeec306373419b57',
     'a402513e3282fcb3755c374247a60ee1dc75f3ebcae3366ccf52ac25b53c8923'),
    ('nine-current-lightweight-jones-independent',
     '70fa8ff35d25a6e39ce3078b4e81736af99dd44cdcd4c89a885e2964c4490cf2',
     '1c179ac8eb8f0f548f7d9ab37cc8640eb39256e75afc347e637f5d52d4ec76a0'),
    ('nine-sharing-seed38-weighted-terminal-independent',
     '7b96ad9d85c02281d2e934c6ec03b072dea1ed4ba5d92a973c13f148759f6570',
     '9a4acbf888eab951409808ca15124d50f9a4e3c27ddb92c73a1d1f569670f8ad'),
)
for name, script_pin, result_pin in audits:
    q = D / 'reviews' / name
    if sha(q / 'check.py') != script_pin or sha(q / 'result.json') != result_pin:
        raise RuntimeError(('audit pin mismatch', name))
    r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')],
                       capture_output=True, timeout=300)
    if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
        raise RuntimeError(('audit failed', name, r.returncode, r.stderr.decode(errors='replace')))

base = Path('/tmp/nine-sharing-norm38-ipra-endpoint-check-20261106/lib/DiophantineConsistency')
selected = {
    'Norm38IPRAEndpoint': ('/tmp/nine-sharing-norm38-ipra-endpoint-check-20261106/lib/DiophantineConsistency/Norm38IPRAEndpoint.olean', '570952bced71ff043c7fa9f0f84af3e99b8a6fea2f373651f12c01e7e6c72125'),
    'ModelJonesSyntax': ('/tmp/nine-light-jones-probe-20261105/lib/DiophantineConsistency/ModelJonesSyntax.olean', 'ca320ae03c5aece08482a0eb125d58c12d371ce524cce685428b0550a96c5171'),
    'SharingSeed38': ('/tmp/nine-sharing-seed38-weighted-retry-20261105/lib/DiophantineConsistency/SharingSeed38.olean', '0e93450158f72a8c5bed63c3168110d77df8accbead1e0f1245aacd0e7732498'),
    'SharingSeed38Syntax': ('/tmp/nine-sharing-seed38-weighted-retry-20261105/lib/DiophantineConsistency/SharingSeed38Syntax.olean', '15d083f7db48c3085a61b4c6d387c6661fe5e67ed2013026c0e475f7c19450af'),
}
out = {}
for name, (target, digest) in selected.items():
    path = base / (name + '.olean')
    if not path.is_file() or str(path.resolve()) != target or sha(path) != digest:
        raise RuntimeError(('selected provider drift', name, str(path)))
    out['DiophantineConsistency.' + name] = {'realpath': target, 'sha256': digest}
if os.path.lexists(base / 'Norm38NamedFormula.olean'):
    raise RuntimeError('output shadows base')
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY', 'selected': out,
                  'scope': 'Selected audited endpoint, Jones and seed producers and overlay routes; no Lean, document binding or complete dynamic ancestry.'}, indent=2, sort_keys=True))
