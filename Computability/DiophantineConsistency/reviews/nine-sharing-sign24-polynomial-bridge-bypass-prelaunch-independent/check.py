#!/usr/bin/env python3
"""Review sign26-bypass bridge proposal and audited provider union."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign24-polynomial-bridge-bypass-check'
draft = research/'nine-sharing-sign24-polynomial-bridge-bypass-draft'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
src = packet/'src/DiophantineConsistency/Sign24BypassPolynomialBridge.lean'
entry, = json.loads((packet/'source-manifest.json').read_text())['rows']
assert entry['module'] == 'DiophantineConsistency.Sign24BypassPolynomialBridge'
assert digest(src) == digest(draft/'Sign24BypassPolynomialBridge.lean') == entry['source_sha256']
assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M) == entry['imports'] == [
    'DiophantineConsistency.Sign24ExpressionEquivalence','DiophantineConsistency.Sign25ExpressionEquivalence',
    'DiophantineConsistency.GenericPolynomialBridgeTransport','DiophantineConsistency.Sign26DirectPolynomialBridge']
s = src.read_text()
assert 'PolynomialBridge Sign24CurrentExpression.expression' in s
assert 'GenericPolynomialBridgeTransport.transfer _ _ ?_ Sign26DirectIPRA.polynomialBridge' in s
assert '(Sign24ExpressionEquivalence.zero_exists_iff (V := V)).trans' in s
assert '(Sign25ExpressionEquivalence.zero_exists_iff (V := V))' in s
for review in ('nine-sharing-sign24-expression-equivalence-terminal-independent',
               'nine-sharing-sign25-expression-equivalence-terminal-frontier-independent',
               'nine-sharing-generic-polynomial-bridge-transport-retry01-terminal-frontier-independent',
               'nine-sharing-sign26-concrete-polynomial-bridge-terminal-frontier-independent'):
    subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
survey = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'provider-union-survey.py')],check=True,capture_output=True,text=True,timeout=120)
assert json.loads(survey.stdout)['status'] == 'PASS'
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','source_sha256':digest(src),'runner_sha256':digest(packet/'run.py'),
                  'scope':'proposed sign24 bridge via transitive zero equivalence and sign26 bridge; no endpoint'},sort_keys=True,indent=2))
