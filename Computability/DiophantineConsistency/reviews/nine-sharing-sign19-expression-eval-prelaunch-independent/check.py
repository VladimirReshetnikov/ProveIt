#!/usr/bin/env python3
"""Review sign20 Fin19 expression/evaluation stages and point providers."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root / 'research'
packet = research/'nine-sharing-sign19-expression-eval-check'
draft = research/'nine-sharing-sign19-expression-eval-draft'
prior = research/'nine-sharing-sign20-expression-eval-check/src/DiophantineConsistency'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
names = ['Sign19AbstractExpressionDef','Sign19AbstractExpressionEval','Sign19CurrentExpressionDef','Sign19CurrentExpressionEval']
imports = [['DiophantineConsistency.Sign32GenericRemoveInput','DiophantineConsistency.SharingSeed19Degree44'],
           ['DiophantineConsistency.Sign19AbstractExpressionDef'],
           ['DiophantineConsistency.Sign19AbstractExpressionEval','DiophantineConsistency.CurrentKernelData2011'],
           ['DiophantineConsistency.Sign19CurrentExpressionDef']]
rows = json.loads((packet/'source-manifest.json').read_text())['rows']
assert [r['module'] for r in rows] == ['DiophantineConsistency.'+n for n in names]
for row,name,expected in zip(rows,names,imports):
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    assert digest(src) == digest(draft/(name+'.lean')) == row['source_sha256']
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M) == row['imports'] == expected
    old = (prior/(name.replace('Sign19','Sign20')+'.lean')).read_text()
    assert src.read_text() == old.replace('Sign20','Sign19').replace('SharingSeed20Degree20','SharingSeed19Degree44').replace('Fin 20','Fin 19')
definition = (draft/(names[0]+'.lean')).read_text()
evaluation = (draft/(names[1]+'.lean')).read_text()
assert 'Sign32GenericRemoveInput.removeInput (SharingSeed19Degree44.seed p)' in definition
assert 'Fin.cons (1 : V) w i' in evaluation and 'Sign32GenericRemoveInput.eval_removeInput' in evaluation
assert digest(packet/'run.py') == '3d55de24428452471421a78c00504ab1aa8c7ff23f9c0656048bd5171c864ab6'
r=(packet/'run.py').read_text();assert "if local=='Sign32GenericRemoveInput':" in r and "elif local in ('Sign19AbstractExpressionDef','Sign19AbstractExpressionEval','Sign19CurrentExpressionDef','Sign19CurrentExpressionEval'):" in r and "elif local in seeddata['observed']:" in r
assert "'-M2800'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
upstream = root/'reviews/nine-sharing-sign19-staged-syntax-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':4,'runner_sha256':digest(packet/'run.py'),
                  'scope':'Fin19 expression/evaluation source only; selected partial provider observations, no endpoint'},sort_keys=True,indent=2))
