#!/usr/bin/env python3
"""Review sign21 polynomial-bridge transport and provider union."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign21-concrete-polynomial-bridge-check'
draft = research/'nine-sharing-sign21-concrete-polynomial-bridge-draft'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
src = packet/'src/DiophantineConsistency/Sign21DirectPolynomialBridge.lean'
entry, = json.loads((packet/'source-manifest.json').read_text())['rows']
assert entry['module'] == 'DiophantineConsistency.Sign21DirectPolynomialBridge'
assert digest(src) == digest(draft/'Sign21DirectPolynomialBridge.lean') == entry['source_sha256']
assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M) == entry['imports'] == [
    'DiophantineConsistency.Sign21ExpressionEquivalence','DiophantineConsistency.GenericPolynomialBridgeTransport',
    'DiophantineConsistency.Sign22DirectPolynomialBridge']
s = src.read_text()
assert 'HAExpressionAssembly.PolynomialBridge Sign21CurrentExpression.expression' in s
assert 'GenericPolynomialBridgeTransport.transfer _ _ ?_ Sign22DirectIPRA.polynomialBridge' in s
assert 'Sign21ExpressionEquivalence.zero_exists_iff (V := V)' in s
for review in ('nine-sharing-sign21-expression-equivalence-terminal-independent',
               'nine-sharing-generic-polynomial-bridge-transport-retry01-terminal-frontier-independent',
               'nine-sharing-sign22-concrete-polynomial-bridge-terminal-independent'):
    subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
survey = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'provider-union-survey.py')],check=True,capture_output=True,text=True,timeout=120)
observed = json.loads(survey.stdout)
assert observed['status'] == 'PASS'
assert observed['producers']['generic']['extra_count'] == 20 and observed['producers']['sign22']['extra_count'] == 361
runner = (packet/'run.py').read_text()
assert "need(not OUT.exists(),'output exists')" in runner and "'-M3600'" in runner
assert 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in runner and '5_000_000_000' in runner
assert "outer=o['author_observed_numeric_outer_exit']" in (packet/'provider-union-survey.py').read_text()
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','source_sha256':digest(src),'runner_sha256':digest(packet/'run.py'),
                  'scope':'proposed sign21 polynomial bridge via sign22 zero equivalence; no endpoint'},sort_keys=True,indent=2))
