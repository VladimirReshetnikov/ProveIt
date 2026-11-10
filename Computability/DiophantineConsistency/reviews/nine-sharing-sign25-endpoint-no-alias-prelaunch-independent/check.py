#!/usr/bin/env python3
"""Audit sign25 no-alias endpoint candidate and no-Lean guard preflight."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root / 'research'
packet = research / 'nine-sharing-sign25-endpoint-no-alias-check'
draft = research / 'nine-sharing-sign25-endpoint-no-alias-draft'
previous = research / 'nine-sharing-sign25-endpoint-check'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
names = ['Sign25DirectNoAliasNative', 'Sign25DirectNoAliasStandard', 'Sign25DirectNoAliasTranslated']
manifest = packet / 'source-manifest.json'
rows = json.loads(manifest.read_text())['rows']
assert digest(manifest) == '2952924dc5c8323f8ae0a6fd5ed112b22d8648843b91a9bcb8c3b6e7d7ff69fc'
assert [r['module'] for r in rows] == ['DiophantineConsistency.' + n for n in names]
contents = []
for name, row in zip(names, rows):
    source = packet / 'src/DiophantineConsistency' / (name + '.lean')
    assert digest(source) == digest(draft / (name + '.lean')) == row['source_sha256']
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$', source.read_text(), re.M) == row['imports']
    assert (root.parents[1] / row['source']).is_file()
    contents.append(source.read_text())
assert [r['imports'] for r in rows] == [
    ['DiophantineConsistency.Sign25DirectPolynomialBridge', 'DiophantineConsistency.IPRAExpressionNative'],
    ['DiophantineConsistency.Sign25DirectNoAliasNative', 'DiophantineConsistency.IPRAStandardTheory'],
    ['DiophantineConsistency.Sign25DirectNoAliasStandard']]
assert 'def expression' not in ''.join(contents)
assert 'nativeTheory ⊢' in contents[0] and 'nativeNoZero Sign25CurrentExpression.expression' in contents[0]
assert 'equivalence_of_bridge Sign25CurrentExpression.expression' in contents[0] and 'Sign25DirectIPRA.polynomialBridge' in contents[0]
assert 'standardTheory ⊢' in contents[1] and '(IPRAStandardTheory.provable_iff _).2 native_equivalence' in contents[1]
assert 'standardTheory ⊢' in contents[2] and '(Semiformula.lMap embedding sourceSentence)ᴺ' in contents[2]
expected = (previous / 'run.py').read_text()
replacements = [
    ('c5de8b265cfbb4fbc75bd903f67e411dff8798d8144fd4d5fdfbafff79e10dd8', digest(manifest)),
    ('/tmp/nine-sharing-sign25-endpoint-check-20261106', '/tmp/nine-sharing-sign25-endpoint-no-alias-20261109'),
    ("'Sign25NativeExpression','Sign25DirectNative','Sign25DirectStandard','Sign25DirectTranslated'", ','.join(repr(n) for n in names)),
    ("'Sign25NativeExpression','Sign25DirectNative','Sign25DirectStandard'", ','.join(repr(n) for n in names[:-1])),
    ('Bounded sign26 direct endpoint diagnostic', 'Bounded sign25 no-alias endpoint attempt'),
    ('PASS sign25 direct endpoint diagnostic', 'PASS sign25 no-alias endpoint attempt')]
for old, new in replacements:
    assert expected.count(old) == 1
    expected = expected.replace(old, new)
assert expected == (packet / 'run.py').read_text()
assert digest(packet / 'run.py') == 'd36f5bd20ed4f8d7a6a414f309a499d2520c94493ffa3e78ba7e7f0e3aae4ccd'
assert digest(packet / 'framework-survey.py') == digest(previous / 'framework-survey.py')
preflight = subprocess.run([sys.executable, '-I', '-S', '-B', str(packet / 'run.py'), '--preflight'], capture_output=True, text=True, timeout=180)
assert preflight.returncode == 0 and not preflight.stderr
assert json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status': 'PASS_PRELAUNCH', 'preflight_exit': 0, 'stages': names,
                  'runner_sha256': digest(packet / 'run.py'), 'manifest_sha256': digest(manifest),
                  'scope': 'proposed native, standard and translated Fin25 endpoints; no Lean compilation'}, sort_keys=True, indent=2))
