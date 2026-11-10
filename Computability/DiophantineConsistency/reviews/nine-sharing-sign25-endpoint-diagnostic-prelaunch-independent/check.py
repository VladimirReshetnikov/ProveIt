#!/usr/bin/env python3
"""Independent prelaunch audit; checks sources and runner without Lean."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root / 'research'
packet = research / 'nine-sharing-sign25-endpoint-diagnostic-check'
draft = research / 'nine-sharing-sign25-endpoint-diagnostic-draft'
previous = research / 'nine-sharing-sign25-endpoint-check'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
names = ['Sign25DiagImport', 'Sign25DiagExpression', 'Sign25DiagBridge', 'Sign25DiagAxioms']
manifest = packet / 'source-manifest.json'
rows = json.loads(manifest.read_text())['rows']
assert digest(manifest) == '4e60a3e4a25c56aeaf6251979ba5321188b85d58bf8891df5a95fdd9ddc564ea'
assert [r['module'] for r in rows] == ['DiophantineConsistency.' + n for n in names]
for i, (name, row) in enumerate(zip(names, rows)):
    source = packet / 'src/DiophantineConsistency' / (name + '.lean')
    assert digest(source) == digest(draft / (name + '.lean')) == row['source_sha256']
    assert row['imports'] == ['DiophantineConsistency.' + ('Sign25DirectPolynomialBridge' if i == 0 else names[i-1])]
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$', source.read_text(), re.M) == row['imports']
    assert (root.parents[1] / row['source']).is_file()
source_text = [(packet / 'src/DiophantineConsistency' / (n + '.lean')).read_text() for n in names]
assert 'def expression : Expr (Fin 25) := Sign25CurrentExpression.expression' in source_text[1]
assert 'HAExpressionAssembly.PolynomialBridge expression' in source_text[2]
assert 'Sign25DirectIPRA.polynomialBridge' in source_text[2]
assert '#print axioms DiophantineConsistency.Sign25EndpointDiagnostic.expression_bridge' in source_text[3]
expected = (previous / 'run.py').read_text()
replacements = [
    ('c5de8b265cfbb4fbc75bd903f67e411dff8798d8144fd4d5fdfbafff79e10dd8', digest(manifest)),
    ('/tmp/nine-sharing-sign25-endpoint-check-20261106', '/tmp/nine-sharing-sign25-endpoint-diagnostic-20261109'),
    ("'Sign25NativeExpression','Sign25DirectNative','Sign25DirectStandard','Sign25DirectTranslated'", ','.join(repr(n) for n in names)),
    ("'Sign25NativeExpression','Sign25DirectNative','Sign25DirectStandard'", ','.join(repr(n) for n in names[:-1])),
    ('Bounded sign26 direct endpoint diagnostic', 'Bounded sign25 split-stage bridge diagnostic'),
    ('PASS sign25 direct endpoint diagnostic', 'PASS sign25 split-stage bridge diagnostic')]
for old, new in replacements:
    assert expected.count(old) == 1
    expected = expected.replace(old, new)
assert expected == (packet / 'run.py').read_text()
assert digest(packet / 'run.py') == '213c1ca053ba8a44e8af4378e1bbb92e22967f1f96745f957919cf26f4eae7cf'
assert digest(packet / 'framework-survey.py') == digest(previous / 'framework-survey.py')
preflight = subprocess.run([sys.executable, '-I', '-S', '-B', str(packet / 'run.py'), '--preflight'],
                           capture_output=True, text=True, timeout=180)
assert preflight.returncode == 0 and not preflight.stderr
assert json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status': 'PASS_PRELAUNCH', 'preflight_exit': 0, 'stages': names,
                  'runner_sha256': digest(packet / 'run.py'), 'manifest_sha256': digest(manifest),
                  'scope': 'split import, alias, bridge and axiom report diagnostic only; no endpoint or exact cause'}, sort_keys=True, indent=2))
