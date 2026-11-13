#!/usr/bin/env python3
"""Recheck historical source provenance and replay frozen finite auditor in isolation."""
import ast
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[1]
REPO = PROJECT.parents[1]
RESEARCH = PROJECT / 'research'
DRIFT = RESEARCH / 'normalized106-degree-audit-drift'
REPLAY = RESEARCH / 'normalized106-historical-finite-replay'
COMMIT = '4a1fb8565a4a0f41be9eff68e1b6d9fdd70cb702'
CERT = '16358ce2d453371d2f2d1cad8ab22136ea61ec9ff77200a55264ad56d4a57879'
def digest(data): return hashlib.sha256(data).hexdigest()
def need(condition, message):
    if not condition: raise RuntimeError(message)

frozen = {
    REPLAY / 'replay.py': '279391ee3495666b3a36c071173eeb8b8ca478d0719a931c15622435f85ffeb0',
    REPLAY / 'observations/attempt01/result.json': 'efb69ba7f0177db329772da9b2fdda4cd860649d7716902a7f285b849624ed92',
    REPLAY / 'observations/attempt01/outer-terminal.json': '96c732de8f30ba79ecef33a979ba4ea218e138afb30290bdeae53bc5695483a6',
    REPLAY / 'observations/attempt01/stdout': '3f3a27b1cbd4a1e496d3812fd7eee6ffd6640ed6bdeb99dfb4cb2e3a2ac22b22',
}
for path, expected in frozen.items(): need(digest(path.read_bytes()) == expected, 'frozen file mismatch ' + str(path))
need((REPLAY / 'observations/attempt01/stderr').read_bytes() == b'', 'saved stderr not empty')
tree = ast.parse((REPLAY / 'replay.py').read_text())
inputs = next(ast.literal_eval(n.value) for n in tree.body if isinstance(n, ast.Assign)
              and any(isinstance(t, ast.Name) and t.id == 'INPUTS' for t in n.targets))
need(len(inputs) == 16, 'expected 16 inputs')
paths = ['CarrierNormalizedProduct106.lean', 'CarrierScaledAuxiliary118.lean']
relative = [f'Computability/DiophantineConsistency/Lean/DiophantineConsistency/{p}' for p in paths]
for name, path in zip(paths, relative):
    historic = subprocess.run(['git', 'show', COMMIT + ':' + path], cwd=REPO, check=True, stdout=subprocess.PIPE).stdout
    need(historic == (DRIFT / ('historical-' + name)).read_bytes(), 'git extraction mismatch')
diff = subprocess.run(['git', 'diff', COMMIT, '--', *relative], cwd=REPO, check=True, stdout=subprocess.PIPE).stdout
need(diff == (DRIFT / 'source-diff.patch').read_bytes(), 'git diff mismatch')
recorded = json.loads((REPLAY / 'observations/attempt01/result.json').read_text())
need(recorded['status'] == 'PASS' and recorded['inputs_stable'] and recorded['certificate_sha256'] == CERT, 'recorded result mismatch')
need(recorded['inputs'] == {d: {'source': s, 'sha256': h} for d, (s, h) in inputs.items()}, 'recorded input mismatch')
outputs = []
with tempfile.TemporaryDirectory(prefix='normalized106-independent-') as temp:
    root = Path(temp)
    for dst, (source, expected) in inputs.items():
        data = Path(source).read_bytes()
        need(digest(data) == expected, 'source mismatch ' + source)
        target = root / dst
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        need(digest(target.read_bytes()) == expected, 'copy mismatch ' + dst)
    for optimized in (False, True):
        cmd = ['/usr/bin/nice', '-n', '19', sys.executable, '-I', '-S', '-B']
        if optimized: cmd.append('-O')
        result = subprocess.run(cmd + ['audit.py'], cwd=root / 'research/fourteen-normalized-product106',
                                capture_output=True, timeout=120, check=True)
        need(result.stderr == b'', 'auditor stderr')
        value = json.loads(result.stdout)
        need((value['status'], value['variables'], value['operations'], value['degree'], value['certificate_sha256'])
             == ('PASS', 14, 67, 106, CERT), 'auditor result mismatch')
        outputs.append(value)
    for dst, (source, expected) in inputs.items():
        need(digest(Path(source).read_bytes()) == digest((root / dst).read_bytes()) == expected, 'input drift ' + dst)
need(outputs[0] == outputs[1] == recorded['auditor_report'] == json.loads((REPLAY / 'observations/attempt01/stdout').read_bytes()), 'saved or optimized replay mismatch')
print(json.dumps({'status': 'PASS', 'historical_commit': COMMIT, 'inputs': 16,
                  'two_isolated_replays': outputs, 'scope': 'historical finite audit; no Lean or live-source audit'}, sort_keys=True))
