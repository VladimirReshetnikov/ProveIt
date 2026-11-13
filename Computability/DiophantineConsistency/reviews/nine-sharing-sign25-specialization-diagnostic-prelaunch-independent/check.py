#!/usr/bin/env python3
"""Review staged import, proposition and proof-term diagnostics."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign25-specialization-diagnostic-check'
draft = research/'nine-sharing-sign25-specialization-diagnostic-draft'
prior = research/'nine-sharing-sign25-typed-sentence-check/src/DiophantineConsistency'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = packet/'source-manifest.json'
assert digest(manifest) == '8157af08b12439d7b10feac73515e80af0ce54402e22fa0f8856d12bc9823161'
rows = json.loads(manifest.read_text())['rows']
names = ['Sign25GenericStandard','Sign25TypedSentence','Sign25TypedImports','Sign25TypedCheckFormula','Sign25TypedCheckProof']
assert [r['module'] for r in rows] == ['DiophantineConsistency.'+n for n in names]
imports = [['DiophantineConsistency.IPRAExpressionNative','DiophantineConsistency.IPRAStandardTheory'],
           ['DiophantineConsistency.Sign25GenericStandard','DiophantineConsistency.Sign25CurrentExpressionDef']]+[
           ['DiophantineConsistency.Sign25TypedSentence','DiophantineConsistency.Sign25DirectPolynomialBridge']]*3
texts = []
for row,name,expected in zip(rows,names,imports):
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    assert digest(src) == digest(draft/(name+'.lean')) == row['source_sha256']
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M) == row['imports'] == expected
    texts.append(src.read_text())
for i in (0,1): assert texts[i] == (prior/(names[i]+'.lean')).read_text()
assert '#check' not in texts[2] and not re.search(r'(?m)^(?:def|theorem|lemma)\b',texts[2])
assert '#check (IPRAStandardTheory.standardTheory ⊢ sentence 🡘 ∼mappedNativeRefutation embedding)' in texts[3]
assert '#check (Sign25GenericStandard.standard_of_bridge Sign25CurrentExpression.expression' in texts[4]
assert 'Sign25DirectIPRA.polynomialBridge)' in texts[4]
assert not any(re.search(r'(?m)^(?:def|theorem|lemma)\b', t) for t in texts[2:])
runner = packet/'run.py'
assert digest(runner) == 'aed65d2aa512dcea9c415c0bed978d97a037074c9b9c57f1c7fefb0cb60a4609'
assert "elif local=='Sign25CurrentExpressionDef':" in runner.read_text()
assert "need(check_expression()==expression_data,'expression final drift')" in runner.read_text()
assert digest(packet/'expression-survey.py') == digest(draft/'expression-survey.py')
subprocess.run([sys.executable,'-I','-S','-B',str(packet/'expression-survey.py')],check=True,capture_output=True,timeout=120)
upstream = root/'reviews/nine-sharing-sign25-concrete-polynomial-bridge-terminal-frontier-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':digest(runner),'stages':5,
                  'scope':'two theorem producers and independent import/formula/proof-term diagnostics; no specialized endpoint'},sort_keys=True,indent=2))
