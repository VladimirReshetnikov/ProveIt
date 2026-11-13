#!/usr/bin/env python3
"""Review all fifteen q3 transfer source rows and guarded preflight."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root / 'research'
packet = research / 'nine-sharing-sign24-transfers-check'
draft = research / 'nine-sharing-sign24-model-bridge-draft'
old_path = research / 'nine-sharing-sign25-octic-ell-candidate/seed.json'
new_path = research / 'nine-sharing-sign24-octic-q3-candidate/seed.json'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert digest(old_path) == 'c95637ae24a57dba0ae1113a8256ed6f12d33f416f035f9cd4f92cffdbf59fc8'
assert digest(new_path) == '24a6dcf05b96112cfa332aafe4790a367c44b9a0cc033a74197f92d3520ab865'
old = json.loads(old_path.read_text())['residuals'][1:]
new = json.loads(new_path.read_text())['residuals']
assert len(old) == len(new) == 15
ports = {'beta':0, 'K0':1, 'MC':2, 'MF':3}
def render(t):
    op, *a = t
    if op == 'var': return '(Expr.var ' + str(a[0]) + ')'
    if op == 'num': return '(Expr.constant (' + str(a[0]) + ' : ℤ))'
    if op == 'port': return '(Expr.constant (p ' + str(ports[a[0]]) + '))'
    assert op in ('add', 'sub', 'mul') and len(a) == 2
    return '(' + render(a[0]) + ' ' + {'add':'+', 'sub':'-', 'mul':'*'}[op] + ' ' + render(a[1]) + ')'
manifest = packet / 'source-manifest.json'
assert digest(manifest) == '3b9af591014414dd21515ba0f35f2a720ca862e3c8d13c156131b464fdb078aa'
entries = json.loads(manifest.read_text())['rows']
assert len(entries) == 3
for stage, entry in enumerate(entries):
    name = f'Sign24Transfers0{stage}'
    assert entry['module'] == 'DiophantineConsistency.' + name
    src = packet / 'src/DiophantineConsistency' / (name + '.lean')
    assert digest(src) == digest(draft / (name + '.lean')) == entry['source_sha256']
    text = src.read_text()
    assert entry['imports'] == re.findall(r'^import ([A-Za-z0-9_.]+)$', text, re.M) == ['DiophantineConsistency.Sign24Coordinate']
    for i in range(stage*5, stage*5+5):
        gate = old[i]['gate']
        assert gate == new[i]['gate']
        for prefix, row, size in [('old',old[i],26),('new',new[i],25)]:
            needle = f'def {prefix}{gate} (p : Fin 4 → ℤ) : Expr (Fin {size}) :=\n  '
            assert text.split(needle,1)[1].splitlines()[0] == render(row['expr'])
        assert f'((SharingSeed25Octic.remainingResiduals p).drop {i}).head? = some (old{gate} p)' in text
        if i == 0: assert f'SharingSeed24Octic.firstResidual p = new{gate} p' in text
        else: assert f'((SharingSeed24Octic.remainingResiduals p).drop {i-1}).head? = some (new{gate} p)' in text
        assert f'theorem {gate}_eval' in text
    assert text.count('(hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)') == 5
coordinate = root / 'reviews/nine-sharing-sign24-coordinate-terminal-independent/check.py'
subprocess.run([sys.executable, '-I', '-S', '-B', str(coordinate)], check=True, capture_output=True, timeout=120)
preflight = subprocess.run([sys.executable, '-I', '-S', '-B', str(packet / 'run.py'), '--preflight'], capture_output=True, text=True, timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH', 'residual_pairs':15, 'runner_sha256':digest(packet / 'run.py'),
                  'scope':'source AST and offsets plus provider point checks; no Lean transfer or model bridge'}, sort_keys=True, indent=2))
