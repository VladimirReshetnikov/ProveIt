#!/usr/bin/env python3
"""Review all thirteen kY transfer source rows and guarded preflight."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign22-transfers-check'
draft = research/'nine-sharing-sign22-model-bridge-draft'
old_path = research/'nine-sharing-sign23-octic-delta-candidate/seed.json'
new_path = research/'nine-sharing-sign22-dodecic-ky-candidate/seed.json'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert digest(old_path) == 'ee6079ea26dd120fab39789f83034947c18e0c8806945a1fc75fca62e1c65d41'
assert digest(new_path) == '3746dacafb661a8bab30caee81ec3b2130915a8b31adf8fe3630f6a541574f37'
all_old = json.loads(old_path.read_text())['residuals']
old = [r for r in all_old if r['gate'] != 'kY']
new = json.loads(new_path.read_text())['residuals']
assert len(old) == len(new) == 13 and len(all_old) == 14
ports = {'beta':0,'K0':1,'MC':2,'MF':3}
def render(t):
    op,*a = t
    if op == 'var': return '(Expr.var '+str(a[0])+')'
    if op == 'num': return '(Expr.constant ('+str(a[0])+' : ℤ))'
    if op == 'port': return '(Expr.constant (p '+str(ports[a[0]])+'))'
    assert op in ('add','sub','mul') and len(a) == 2
    return '('+render(a[0])+' '+{'add':'+','sub':'-','mul':'*'}[op]+' '+render(a[1])+')'
entries = json.loads((packet/'source-manifest.json').read_text())['rows']
assert len(entries) == 2
for stage,entry in enumerate(entries):
    name = f'Sign22Transfers0{stage}'
    assert entry['module'] == 'DiophantineConsistency.'+name
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    assert digest(src) == digest(draft/(name+'.lean')) == entry['source_sha256']
    text = src.read_text()
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$',text,re.M) == entry['imports'] == ['DiophantineConsistency.Sign22Coordinate']
    for i in range(stage*7,min(stage*7+7,13)):
        gate = old[i]['gate']
        assert gate == new[i]['gate']
        for prefix,row,size in [('old',old[i],24),('new',new[i],23)]:
            needle = f'def {prefix}{gate} (p : Fin 4 → ℤ) : Expr (Fin {size}) :=\n  '
            assert text.split(needle,1)[1].splitlines()[0] == render(row['expr'])
        oi = next(j for j,r in enumerate(all_old) if r['gate'] == gate)
        if oi == 0: assert f'SharingSeed23Octic.firstResidual p = old{gate} p' in text
        else: assert f'((SharingSeed23Octic.remainingResiduals p).drop {oi-1}).head? = some (old{gate} p)' in text
        if i == 0: assert f'SharingSeed22Dodecic.firstResidual p = new{gate} p' in text
        else: assert f'((SharingSeed22Dodecic.remainingResiduals p).drop {i-1}).head? = some (new{gate} p)' in text
        assert f'theorem {gate}_eval' in text
    assert 'hp0' not in text
upstream = root/'reviews/nine-sharing-sign22-coordinate-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','residual_pairs':13,'runner_sha256':digest(packet/'run.py'),
                  'scope':'source AST and offsets plus provider points; no Lean transfer or full bridge'},sort_keys=True,indent=2))
