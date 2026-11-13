#!/usr/bin/env python3
"""Review sign20/21 direct-expression zero equivalence proposal."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign20-expression-equivalence-check'
draft = research/'nine-sharing-sign20-expression-equivalence-draft'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
source = packet/'src/DiophantineConsistency/Sign20ExpressionEquivalence.lean'
entry, = json.loads((packet/'source-manifest.json').read_text())['rows']
assert entry['module'] == 'DiophantineConsistency.Sign20ExpressionEquivalence'
assert digest(source) == digest(draft/'Sign20ExpressionEquivalence.lean') == entry['source_sha256']
assert re.findall(r'^import ([A-Za-z0-9_.]+)$',source.read_text(),re.M) == entry['imports'] == [
    'DiophantineConsistency.Sign20CurrentExpressionEval', 'DiophantineConsistency.Sign21CurrentExpressionEval',
    'DiophantineConsistency.Sign20CurrentSeedIff']
s = source.read_text()
assert '∃ w : Fin 20 → V, InternalZero Sign20CurrentExpression.expression w' in s
assert '∃ w : Fin 21 → V, InternalZero Sign21CurrentExpression.expression w' in s
assert 'Sign20CurrentExpression.eval_expression' in s and 'Sign21CurrentExpression.eval_expression' in s
assert 'Sign20CurrentSeedIff.exists_same_input (1 : V)' in s
assert 'Fin.cons_self_tail v' in s and 'Fin.tail v' in s
for review in ('nine-sharing-sign20-current-iff-terminal-independent', 'nine-sharing-sign20-expression-eval-terminal-independent', 'nine-sharing-sign21-expression-eval-terminal-independent'):
    subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
survey = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'evaluator-union-survey.py')],check=True,capture_output=True,text=True,timeout=120)
assert json.loads(survey.stdout)['status'] == 'PASS'
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','source_sha256':digest(source),'runner_sha256':digest(packet/'run.py'),
                  'scope':'current-port Fin20/Fin21 zero-existence equivalence proposal, no endpoint'},sort_keys=True,indent=2))
