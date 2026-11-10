#!/usr/bin/env python3
"""Verify the minimal command diagnostic and no-Lean preflight."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root / 'research'
packet = research / 'nine-sharing-sign25-endpoint-minimal-diagnostic-check'
draft = research / 'nine-sharing-sign25-endpoint-minimal-diagnostic-draft'
previous = research / 'nine-sharing-sign25-endpoint-check'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
names = ['Sign25DiagCommand', 'Sign25DiagAlias', 'Sign25DiagAttributes']
manifest = packet / 'source-manifest.json'
rows = json.loads(manifest.read_text())['rows']
assert digest(manifest) == 'f8995a2b813e5ec16681539b6a28670459f806752370995ea1e7bc376e5ac65e'
assert [r['module'] for r in rows] == ['DiophantineConsistency.' + n for n in names]
contents = []
for name, row in zip(names, rows):
    source = packet / 'src/DiophantineConsistency' / (name + '.lean')
    assert digest(source) == digest(draft / (name + '.lean')) == row['source_sha256']
    assert row['imports'] == ['DiophantineConsistency.Sign25DirectPolynomialBridge']
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$', source.read_text(), re.M) == row['imports']
    assert (root.parents[1] / row['source']).is_file()
    contents.append(source.read_text())
assert '#check DiophantineConsistency.Sign25DirectIPRA.polynomialBridge' in contents[0]
assert 'def expression : Expr (Fin 25) := Sign25CurrentExpression.expression' in contents[1]
assert 'attribute [local irreducible]' in contents[2] and 'def expression' not in contents[2]
expected = (previous / 'run.py').read_text()
replacements = [
    ('c5de8b265cfbb4fbc75bd903f67e411dff8798d8144fd4d5fdfbafff79e10dd8', digest(manifest)),
    ('/tmp/nine-sharing-sign25-endpoint-check-20261106', '/tmp/nine-sharing-sign25-endpoint-minimal-diagnostic-20261109'),
    ("'Sign25NativeExpression','Sign25DirectNative','Sign25DirectStandard','Sign25DirectTranslated'", ','.join(repr(n) for n in names)),
    ("'Sign25NativeExpression','Sign25DirectNative','Sign25DirectStandard'", ','.join(repr(n) for n in names[:-1])),
    ('Bounded sign26 direct endpoint diagnostic', 'Bounded sign25 minimal command diagnostic'),
    ('PASS sign25 direct endpoint diagnostic', 'PASS sign25 minimal command diagnostic')]
for old, new in replacements:
    assert expected.count(old) == 1
    expected = expected.replace(old, new)
assert expected == (packet / 'run.py').read_text()
assert digest(packet / 'run.py') == '42413377214db7f883673e6e821bc96256c11b6f15013b396d4e5bd9752f2c97'
assert digest(packet / 'framework-survey.py') == digest(previous / 'framework-survey.py')
preflight = subprocess.run([sys.executable, '-I', '-S', '-B', str(packet / 'run.py'), '--preflight'],
                           capture_output=True, text=True, timeout=180)
assert preflight.returncode == 0 and not preflight.stderr
assert json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status': 'PASS_PRELAUNCH', 'preflight_exit': 0, 'stages': names,
                  'runner_sha256': digest(packet / 'run.py'), 'manifest_sha256': digest(manifest),
                  'scope': 'separate command, alias, attributes modules; fail-stop runner; no endpoint'}, sort_keys=True, indent=2))
