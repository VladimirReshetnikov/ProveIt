#!/usr/bin/env python3
"""Review all eleven conditional E transfer source rows and guarded preflight."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign20-transfers-check'
draft = research/'nine-sharing-sign20-model-bridge-draft'
old_path = research/'nine-sharing-sign21-degree14-s-candidate/seed.json'
new_path = research/'nine-sharing-sign20-degree20-e-candidate/seed.json'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert digest(old_path) == '85ad59859a6ebc62f8a4de250ac7abf3af904601e8f6c9e696351d5247ea6e81'
assert digest(new_path) == '2593aca2ac701ff9312fe5aff1719bbf4fd29a97e2c3e14642bf137d6ef8bf7d'
all_old = json.loads(old_path.read_text())['residuals']
old = [r for r in all_old if r['gate'] != 'E']
new = json.loads(new_path.read_text())['residuals']
assert len(old) == len(new) == 11 and len(all_old) == 12
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
    name = f'Sign20Transfers0{stage}'
    assert entry['module'] == 'DiophantineConsistency.'+name
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    assert digest(src) == digest(draft/(name+'.lean')) == entry['source_sha256']
    text = src.read_text()
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$',text,re.M) == entry['imports'] == ['DiophantineConsistency.Sign20Coordinate']
    for i in range(stage*6,min(stage*6+6,11)):
        gate = old[i]['gate']
        assert gate == new[i]['gate']
        for prefix,row,size in [('old',old[i],22),('new',new[i],21)]:
            needle = f'def {prefix}{gate} (p : Fin 4 → ℤ) : Expr (Fin {size}) :=\n  '
            assert text.split(needle,1)[1].splitlines()[0] == render(row['expr'])
        oi = next(j for j,r in enumerate(all_old) if r['gate'] == gate)
        if oi == 0: assert f'SharingSeed21Degree14.firstResidual p = old{gate} p' in text
        else: assert f'((SharingSeed21Degree14.remainingResiduals p).drop {oi-1}).head? = some (old{gate} p)' in text
        if i == 0: assert f'SharingSeed20Degree20.firstResidual p = new{gate} p' in text
        else: assert f'((SharingSeed20Degree20.remainingResiduals p).drop {i-1}).head? = some (new{gate} p)' in text
        assert f'theorem {gate}_eval' in text
    assert text.count('(hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)') == (6 if stage==0 else 5)
upstream = root/'reviews/nine-sharing-sign20-coordinate-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','residual_pairs':11,'runner_sha256':digest(packet/'run.py'),
                  'scope':'source AST and offsets plus provider points; no Lean transfer or full bridge'},sort_keys=True,indent=2))
