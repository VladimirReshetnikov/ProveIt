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
packet = research/'nine-sharing-sign19-transfers-check'
draft = research/'nine-sharing-sign19-model-bridge-draft'
old_path = research/'nine-sharing-sign20-degree20-e-candidate/seed.json'
new_path = research/'nine-sharing-sign19-degree44-y-candidate/seed.json'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert digest(old_path) == '2593aca2ac701ff9312fe5aff1719bbf4fd29a97e2c3e14642bf137d6ef8bf7d'
assert digest(new_path) == '01bae1f7680ce07eb5c041d5ae6a625ead9e79e1c968472521458475a4eb94f1'
all_old = json.loads(old_path.read_text())['residuals']
old = [r for r in all_old if r['gate'] != 'Y']
new = json.loads(new_path.read_text())['residuals']
assert len(old) == len(new) == 10 and len(all_old) == 11
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
    name = f'Sign19Transfers0{stage}'
    assert entry['module'] == 'DiophantineConsistency.'+name
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    assert digest(src) == digest(draft/(name+'.lean')) == entry['source_sha256']
    text = src.read_text()
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$',text,re.M) == entry['imports'] == ['DiophantineConsistency.Sign19Coordinate']
    for i in range(stage*5,min(stage*5+5,10)):
        gate = old[i]['gate']
        assert gate == new[i]['gate']
        for prefix,row,size in [('old',old[i],21),('new',new[i],20)]:
            needle = f'def {prefix}{gate} (p : Fin 4 → ℤ) : Expr (Fin {size}) :=\n  '
            assert text.split(needle,1)[1].splitlines()[0] == render(row['expr'])
        oi = next(j for j,r in enumerate(all_old) if r['gate'] == gate)
        if oi == 0: assert f'SharingSeed20Degree20.firstResidual p = old{gate} p' in text
        else: assert f'((SharingSeed20Degree20.remainingResiduals p).drop {oi-1}).head? = some (old{gate} p)' in text
        if i == 0: assert f'SharingSeed19Degree44.firstResidual p = new{gate} p' in text
        else: assert f'((SharingSeed19Degree44.remainingResiduals p).drop {i-1}).head? = some (new{gate} p)' in text
        assert f'theorem {gate}_eval' in text
    assert text.count('(hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)') == 5
upstream = root/'reviews/nine-sharing-sign19-coordinate-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
runner=packet/'run.py';assert digest(runner)=='3c638dd5d67a6ce64a4ad5d1f0618b82e721c8ee280f515f167fe748a77cd65a'
r=runner.read_text();assert "if local=='Sign19Coordinate':" in r and "'-M2800'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','residual_pairs':10,'runner_sha256':digest(packet/'run.py'),
                  'scope':'source AST and offsets plus provider points; no Lean transfer or full bridge'},sort_keys=True,indent=2))
