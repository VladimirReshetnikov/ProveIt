#!/usr/bin/env python3
"""Review sign22 Fin22 expression/evaluation stages and point providers."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root / 'research'
packet = research/'nine-sharing-sign22-expression-eval-check'
draft = research/'nine-sharing-sign22-expression-eval-draft'
prior = research/'nine-sharing-sign23-expression-eval-check/src/DiophantineConsistency'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
names = ['Sign22AbstractExpressionDef','Sign22AbstractExpressionEval','Sign22CurrentExpressionDef','Sign22CurrentExpressionEval']
imports = [['DiophantineConsistency.Sign32GenericRemoveInput','DiophantineConsistency.SharingSeed22Dodecic'],
           ['DiophantineConsistency.Sign22AbstractExpressionDef'],
           ['DiophantineConsistency.Sign22AbstractExpressionEval','DiophantineConsistency.CurrentKernelData2011'],
           ['DiophantineConsistency.Sign22CurrentExpressionDef']]
rows = json.loads((packet/'source-manifest.json').read_text())['rows']
assert [r['module'] for r in rows] == ['DiophantineConsistency.'+n for n in names]
for row,name,expected in zip(rows,names,imports):
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    assert digest(src) == digest(draft/(name+'.lean')) == row['source_sha256']
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M) == row['imports'] == expected
    old = (prior/(name.replace('Sign22','Sign23')+'.lean')).read_text()
    assert src.read_text() == old.replace('Sign23','Sign22').replace('SharingSeed23Octic','SharingSeed22Dodecic').replace('Fin 23','Fin 22')
definition = (draft/(names[0]+'.lean')).read_text()
evaluation = (draft/(names[1]+'.lean')).read_text()
assert 'Sign32GenericRemoveInput.removeInput (SharingSeed22Dodecic.seed p)' in definition
assert 'Fin.cons (1 : V) w i' in evaluation and 'Sign32GenericRemoveInput.eval_removeInput' in evaluation
assert digest(packet/'run.py') == 'dbcda60d8af098f09a1092490940c60658601e6670957c9590c08e4f9b8d56b2'
upstream = root/'reviews/nine-sharing-sign22-seed-squares-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':4,'runner_sha256':digest(packet/'run.py'),
                  'scope':'Fin22 expression/evaluation source only; selected partial provider observations, no endpoint'},sort_keys=True,indent=2))
