#!/usr/bin/env python3
"""Review pretyped full-assertion staging without introducing assumptions."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign25-pretyped-assertion-check'
draft = research/'nine-sharing-sign25-pretyped-assertion-draft'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = packet/'source-manifest.json'
assert digest(manifest) == '5f61aacbe7ad832e2d4129289c3c40c9e29325fffeb025c82b6a721bf6b2863a'
rows = json.loads(manifest.read_text())['rows']
names = ['Sign25GenericStandard','Sign25TypedAssertion','Sign25AssertionStandard','Sign25AssertionCurrent']
imports = [['DiophantineConsistency.IPRAExpressionNative','DiophantineConsistency.IPRAStandardTheory'],
           ['DiophantineConsistency.Sign25GenericStandard','DiophantineConsistency.Sign25CurrentExpressionDef'],
           ['DiophantineConsistency.Sign25TypedAssertion','DiophantineConsistency.Sign25DirectPolynomialBridge'],
           ['DiophantineConsistency.Sign25AssertionStandard']]
texts = []
for row,name,expected in zip(rows,names,imports):
    assert row['module'] == 'DiophantineConsistency.'+name
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    assert digest(src) == digest(draft/(name+'.lean')) == row['source_sha256']
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M) == row['imports'] == expected
    assert not re.search(r'(?m)^\s*(axiom|opaque)\b',src.read_text())
    texts.append(src.read_text())
assert '(hp : HAExpressionAssembly.PolynomialBridge e)' in texts[0]
assert '(hφ : φ = (IPRAExpressionNative.nativeNoZero e 🡘 ∼mappedNativeRefutation embedding))' in texts[0]
assert 'rw [hφ]' in texts[0] and 'exact standard_of_bridge e hp' in texts[0]
assert 'def assertion : Sentenceᵢ language :=' in texts[1] and 'theorem assertion_def' in texts[1] and ':= rfl' in texts[1]
assert 'Sign25DirectIPRA.polynomialBridge assertion assertion_def' in texts[2]
assert 'rw [← assertion_def]' in texts[3] and 'exact standard_assertion' in texts[3]
runner = packet/'run.py'
assert digest(runner) == '516b079b448dc30a15ebe292eacfc4d72062185753a6b71ee7febb6ea32d1a7f'
assert "elif local=='Sign25CurrentExpressionDef':" in runner.read_text()
assert "need(check_expression()==expression_data,'expression final drift')" in runner.read_text()
subprocess.run([sys.executable,'-I','-S','-B',str(packet/'expression-survey.py')],check=True,capture_output=True,timeout=120)
upstream = root/'reviews/nine-sharing-sign25-concrete-polynomial-bridge-terminal-frontier-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':digest(runner),'stages':4,
                  'scope':'full assertion staged with explicit equality; no compiled endpoint or added axiom'},sort_keys=True,indent=2))
