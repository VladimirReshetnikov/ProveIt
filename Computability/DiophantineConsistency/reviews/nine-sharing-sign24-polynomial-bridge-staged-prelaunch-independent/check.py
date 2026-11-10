#!/usr/bin/env python3
"""Review conditional sign24 bridge factoring and direct provider union."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign24-polynomial-bridge-staged-check'
draft = research/'nine-sharing-sign24-polynomial-bridge-staged-draft'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
rows = json.loads((packet/'source-manifest.json').read_text())['rows']
names = ['Sign24BridgeConditional','Sign24BridgeStaged']
imports = [['DiophantineConsistency.Sign24ExpressionEquivalence','DiophantineConsistency.GenericPolynomialBridgeTransport'],
           ['DiophantineConsistency.Sign24BridgeConditional','DiophantineConsistency.Sign25DirectPolynomialBridge']]
texts = []
assert [r['module'] for r in rows] == ['DiophantineConsistency.'+n for n in names]
for row,name,expected in zip(rows,names,imports):
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    assert digest(src) == digest(draft/(name+'.lean')) == row['source_sha256']
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M) == row['imports'] == expected
    texts.append(src.read_text())
assert '(hb : HAExpressionAssembly.PolynomialBridge Sign25CurrentExpression.expression)' in texts[0]
assert 'GenericPolynomialBridgeTransport.transfer _ _ ?_ hb' in texts[0]
assert 'Sign24ExpressionEquivalence.zero_exists_iff (V := V)' in texts[0]
assert 'transfer_from_sign25 Sign25DirectIPRA.polynomialBridge' in texts[1]
for review in ('nine-sharing-sign24-expression-equivalence-terminal-independent',
               'nine-sharing-generic-polynomial-bridge-transport-retry01-terminal-frontier-independent',
               'nine-sharing-sign25-concrete-polynomial-bridge-terminal-frontier-independent',
               'nine-sharing-sign24-concrete-polynomial-bridge-terminal-independent'):
    subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
survey = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'provider-union-survey.py')],check=True,capture_output=True,text=True,timeout=120)
assert json.loads(survey.stdout)['status'] == 'PASS'
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':2,'runner_sha256':digest(packet/'run.py'),
                  'scope':'conditional transport then proposed bridge instantiation; no Lean endpoint'},sort_keys=True,indent=2))
