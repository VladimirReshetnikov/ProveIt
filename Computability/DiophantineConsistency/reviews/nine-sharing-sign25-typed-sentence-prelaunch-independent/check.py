#!/usr/bin/env python3
"""Review pretyped-sentence endpoint staging and direct provider routing."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign25-typed-sentence-check'
draft = research/'nine-sharing-sign25-typed-sentence-draft'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = packet/'source-manifest.json'
assert digest(manifest) == 'd5900df9d85ad04c8913ea7bad3175ea32c3c7898f223b501300c8f1431bae3f'
rows = json.loads(manifest.read_text())['rows']
names = ['Sign25GenericStandard','Sign25TypedSentence','Sign25TypedStandard','Sign25TypedStandardCurrent']
imports = [['DiophantineConsistency.IPRAExpressionNative','DiophantineConsistency.IPRAStandardTheory'],
           ['DiophantineConsistency.Sign25GenericStandard','DiophantineConsistency.Sign25CurrentExpressionDef'],
           ['DiophantineConsistency.Sign25TypedSentence','DiophantineConsistency.Sign25DirectPolynomialBridge'],
           ['DiophantineConsistency.Sign25TypedStandard']]
texts = []
for row,name,expected in zip(rows,names,imports):
    assert row['module'] == 'DiophantineConsistency.'+name
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    assert digest(src) == digest(draft/(name+'.lean')) == row['source_sha256']
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M) == row['imports'] == expected
    texts.append(src.read_text())
previous = research/'nine-sharing-sign25-generic-standard-retry-check/src/DiophantineConsistency/Sign25GenericStandard.lean'
assert texts[0] == previous.read_text()
assert 'def sentence : Sentenceᵢ language :=' in texts[1] and 'theorem sentence_def' in texts[1]
assert 'nativeNoZero Sign25CurrentExpression.expression' in texts[1]
assert 'rw [sentence_def]' in texts[2] and 'Sign25DirectIPRA.polynomialBridge' in texts[2]
assert 'rw [← sentence_def]' in texts[3] and 'exact standard_typed' in texts[3]
runner = packet/'run.py'
assert digest(runner) == '1f44f4c97ea3c4c14bf1200abf9b4da68cab9925d589934dc13ebf8f09afc10e'
r = runner.read_text()
assert "elif local=='Sign25CurrentExpressionDef':" in r and "expected_hash=expression_data['object_sha256']" in r
assert "need(check_expression()==expression_data,'expression final drift')" in r
assert "for row in base['rows']:" in r and "base['status']=='PASS'" in r
assert digest(packet/'expression-survey.py') == digest(draft/'expression-survey.py')
survey = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'expression-survey.py')],capture_output=True,text=True,check=True,timeout=120)
assert json.loads(survey.stdout)['status'] == 'PASS'
upstream = root/'reviews/nine-sharing-sign25-concrete-polynomial-bridge-terminal-frontier-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':digest(runner),'stages':4,
                  'scope':'candidate generic/typed sentence/standard endpoint staging; no compiled endpoint'},sort_keys=True,indent=2))
