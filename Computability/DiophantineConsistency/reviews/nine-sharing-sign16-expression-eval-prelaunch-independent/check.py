#!/usr/bin/env python3
"""Review sign20 Fin16 expression/evaluation stages and point providers."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root / 'research'
packet = research/'nine-sharing-sign16-expression-eval-check'
draft = research/'nine-sharing-sign16-expression-eval-draft'
prior = research/'nine-sharing-sign17-expression-eval-check/src/DiophantineConsistency'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
names = ['Sign16AbstractExpressionDef','Sign16AbstractExpressionEval','Sign16CurrentExpressionDef','Sign16CurrentExpressionEval']
imports = [['DiophantineConsistency.Sign32GenericRemoveInput','DiophantineConsistency.SharingSeed16Degree112'],
           ['DiophantineConsistency.Sign16AbstractExpressionDef'],
           ['DiophantineConsistency.Sign16AbstractExpressionEval','DiophantineConsistency.CurrentKernelData2011'],
           ['DiophantineConsistency.Sign16CurrentExpressionDef']]
rows = json.loads((packet/'source-manifest.json').read_text())['rows']
assert [r['module'] for r in rows] == ['DiophantineConsistency.'+n for n in names]
for row,name,expected in zip(rows,names,imports):
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    assert digest(src) == digest(draft/(name+'.lean')) == row['source_sha256']
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M) == row['imports'] == expected
    old = (prior/(name.replace('Sign16','Sign17')+'.lean')).read_text()
    assert src.read_text() == old.replace('Sign17','Sign16').replace('SharingSeed17Degree96','SharingSeed16Degree112').replace('Fin 17','Fin 16')
definition = (draft/(names[0]+'.lean')).read_text()
evaluation = (draft/(names[1]+'.lean')).read_text()
assert 'Sign32GenericRemoveInput.removeInput (SharingSeed16Degree112.seed p)' in definition
assert 'Fin.cons (1 : V) w i' in evaluation and 'Sign32GenericRemoveInput.eval_removeInput' in evaluation
assert digest(packet/'run.py') == '80847dbaeb0ceef14d75be63818050f9980825fbedd4f30c01fb313ed2fa1dda'
r=(packet/'run.py').read_text();assert "if local=='Sign32GenericRemoveInput':" in r and "elif local in ('Sign16AbstractExpressionDef','Sign16AbstractExpressionEval','Sign16CurrentExpressionDef','Sign16CurrentExpressionEval'):" in r and "elif local in seeddata['observed']:" in r
assert "'-M2800'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
upstream = root/'reviews/nine-sharing-sign16-staged-syntax-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':4,'runner_sha256':digest(packet/'run.py'),
                  'scope':'Fin16 expression/evaluation source only; selected partial provider observations, no endpoint'},sort_keys=True,indent=2))
