#!/usr/bin/env python3
"""Review generic standard derivability and current specialization sources."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root / 'research'
packet = research / 'nine-sharing-sign25-generic-standard-retry-check'
draft = research / 'nine-sharing-sign25-generic-standard-retry-draft'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = packet / 'source-manifest.json'
assert digest(manifest) == '999f134fefe139cc9127e78f987e9a52eec3ab131ad225981daf483bd7c7e9a6'
rows = json.loads(manifest.read_text())['rows']
names = ['Sign25GenericStandard','Sign25GenericStandardCurrent','Sign25GenericStandardTranslated']
imports = [['DiophantineConsistency.IPRAExpressionNative','DiophantineConsistency.IPRAStandardTheory'],
           ['DiophantineConsistency.Sign25GenericStandard','DiophantineConsistency.Sign25DirectPolynomialBridge'],
           ['DiophantineConsistency.Sign25GenericStandardCurrent']]
texts = []
for row,name,expected in zip(rows,names,imports):
    assert row['module'] == 'DiophantineConsistency.'+name
    src = packet / 'src/DiophantineConsistency' / (name + '.lean')
    assert digest(src) == digest(draft / (name + '.lean')) == row['source_sha256']
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M) == row['imports'] == expected
    texts.append(src.read_text())
    prior = (research / 'nine-sharing-sign25-generic-standard-check/src/DiophantineConsistency' / (name + '.lean')).read_text()
    if name == names[0]: prior = prior.replace('open AdaptiveEquationSyntax2011 ModelDifferenceRing PRALanguage IPRANativeTheory', 'open PRALanguage IPRANativeTheory')
    assert src.read_text() == prior
assert 'theorem standard_of_bridge {n : ℕ} (e : Expr (Fin n))' in texts[0]
assert '(hp : HAExpressionAssembly.PolynomialBridge e)' in texts[0]
assert 'IPRAStandardTheory.transfer IPRAStandardTheory.native_axiom' in texts[0]
assert 'IPRAExpressionNative.equivalence_of_bridge e hp' in texts[0]
assert 'standard_of_bridge Sign25CurrentExpression.expression Sign25DirectIPRA.polynomialBridge' in texts[1]
assert '(Semiformula.lMap embedding sourceSentence)ᴺ' in texts[2] and 'IPRABoundedRhoZFC.zfcEquiv' in texts[2]
runner = packet/'run.py'
assert digest(runner) == '5c923b5f36b9d2b8393171941c8260a15acc604b720eea76ba31b0dab4fc8242'
assert "base['status']=='PASS'" in runner.read_text() and 'sign25-concrete-polynomial-bridge-check' in runner.read_text()
audit = root/'reviews/nine-sharing-sign25-concrete-polynomial-bridge-terminal-frontier-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(audit)],check=True,capture_output=True,timeout=120)
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':digest(runner),
                  'scope':'generic bridged standard proof, sign25 specialization and translated wrapper proposals; no Lean result'},sort_keys=True,indent=2))
