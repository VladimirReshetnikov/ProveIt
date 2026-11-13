#!/usr/bin/env python3
"""Review the sign19 squares client and independently render its AST rows."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root / 'research'
packet = research / 'nine-sharing-sign19-seed-squares-check'
draft = research / 'nine-sharing-sign19-model-bridge-draft'
candidate = research / 'nine-sharing-sign19-degree44-y-candidate/seed.json'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert digest(candidate) == '01bae1f7680ce07eb5c041d5ae6a625ead9e79e1c968472521458475a4eb94f1'
rows = json.loads(candidate.read_text())['residuals']
assert len(rows) == 10
ports = {'beta': 0, 'K0': 1, 'MC': 2, 'MF': 3}
def render(t):
    op, *a = t
    if op == 'var': return '(Expr.var ' + str(a[0]) + ')'
    if op == 'num': return '(Expr.constant (' + str(a[0]) + ' : ℤ))'
    if op == 'port': return '(Expr.constant (p ' + str(ports[a[0]]) + '))'
    assert op in ('add', 'sub', 'mul') and len(a) == 2
    return '(' + render(a[0]) + ' ' + {'add': '+', 'sub': '-', 'mul': '*'}[op] + ' ' + render(a[1]) + ')'
syntax = (draft / 'SharingSeed19Degree44.lean').read_text()
first = syntax.split('def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 20) :=\n  ', 1)[1].splitlines()[0]
rest = syntax.split('def remainingResiduals (p : Fin 4 → ℤ) : List (Expr (Fin 20)) :=\n  [\n', 1)[1].split('\n  ]', 1)[0]
actual = [first] + [line.strip().removesuffix(',') for line in rest.splitlines()]
assert actual == [render(r['expr']) for r in rows]
assert 'set_option maxHeartbeats 4000000' in syntax
assert 'firstResidual p * firstResidual p +\n    QuarticSyntax.sumExpressions ((remainingResiduals p).map fun e => e * e)' in syntax
manifest = packet / 'source-manifest.json'
assert digest(manifest) == '990008875f0af9bde4699ba4e0b3a431d695281243c71cad961e9c20c5a33b15'
entries = json.loads(manifest.read_text())['rows']
assert [e['module'] for e in entries] == ['DiophantineConsistency.SharingSeed19Degree44', 'DiophantineConsistency.SharingSign19Squares']
for entry in entries:
    name = entry['module'].split('.')[-1]
    source = packet / 'src/DiophantineConsistency' / (name + '.lean')
    assert digest(source) == digest(draft / (name + '.lean')) == entry['source_sha256']
    assert entry['imports'] == re.findall(r'^import ([A-Za-z0-9_.]+)$', source.read_text(), re.M)
assert entries[0]['imports'] == ['DiophantineConsistency.NineFreshJones']
assert entries[1]['imports'] == ['DiophantineConsistency.SharingSeed19Degree44', 'DiophantineConsistency.SharingSign33Squares']
squares = (draft / 'SharingSign19Squares.lean').read_text()
assert 'theorem seed_zero_iff_residuals' in squares and 'SharingSign33Squares.squareSum_zero_iff' in squares
assert digest(packet / 'run.py') == 'bdd1057e7b5850f3fd1fc3ab0bc1e8399c6ee3d894eeffcaa9ed97239a1c99d7'
res = subprocess.run([sys.executable, '-I', '-S', '-B', str(packet / 'run.py'), '--preflight'], capture_output=True, text=True, timeout=180)
assert res.returncode == 0 and not res.stderr and json.loads(res.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status': 'PASS_PRELAUNCH', 'residuals_rendered': 10, 'preflight_exit': 0,
                  'runner_sha256': digest(packet / 'run.py'), 'manifest_sha256': digest(manifest),
                  'scope': 'source transcription and no-Lean preflight; no Lean JSON binding or endpoint'}, sort_keys=True, indent=2))
