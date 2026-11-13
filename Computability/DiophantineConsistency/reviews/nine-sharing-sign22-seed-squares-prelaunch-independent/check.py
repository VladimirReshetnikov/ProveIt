#!/usr/bin/env python3
"""Review the sign22 squares client and independently render its AST rows."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root / 'research'
packet = research / 'nine-sharing-sign22-seed-squares-check'
draft = research / 'nine-sharing-sign22-model-bridge-draft'
candidate = research / 'nine-sharing-sign22-dodecic-ky-candidate/seed.json'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert digest(candidate) == '3746dacafb661a8bab30caee81ec3b2130915a8b31adf8fe3630f6a541574f37'
rows = json.loads(candidate.read_text())['residuals']
assert len(rows) == 13
ports = {'beta': 0, 'K0': 1, 'MC': 2, 'MF': 3}
def render(t):
    op, *a = t
    if op == 'var': return '(Expr.var ' + str(a[0]) + ')'
    if op == 'num': return '(Expr.constant (' + str(a[0]) + ' : ℤ))'
    if op == 'port': return '(Expr.constant (p ' + str(ports[a[0]]) + '))'
    assert op in ('add', 'sub', 'mul') and len(a) == 2
    return '(' + render(a[0]) + ' ' + {'add': '+', 'sub': '-', 'mul': '*'}[op] + ' ' + render(a[1]) + ')'
syntax = (draft / 'SharingSeed22Dodecic.lean').read_text()
first = syntax.split('def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 23) :=\n  ', 1)[1].splitlines()[0]
rest = syntax.split('def remainingResiduals (p : Fin 4 → ℤ) : List (Expr (Fin 23)) :=\n  [\n', 1)[1].split('\n  ]', 1)[0]
actual = [first] + [line.strip().removesuffix(',') for line in rest.splitlines()]
assert actual == [render(r['expr']) for r in rows]
assert 'set_option maxHeartbeats 4000000' in syntax
assert 'firstResidual p * firstResidual p +\n    QuarticSyntax.sumExpressions ((remainingResiduals p).map fun e => e * e)' in syntax
manifest = packet / 'source-manifest.json'
assert digest(manifest) == 'f5cceb24b47f1ad27475b95b8b5c708f5ae4facb371da8550f2dee9593e527a1'
entries = json.loads(manifest.read_text())['rows']
assert [e['module'] for e in entries] == ['DiophantineConsistency.SharingSeed22Dodecic', 'DiophantineConsistency.SharingSign22Squares']
for entry in entries:
    name = entry['module'].split('.')[-1]
    source = packet / 'src/DiophantineConsistency' / (name + '.lean')
    assert digest(source) == digest(draft / (name + '.lean')) == entry['source_sha256']
    assert entry['imports'] == re.findall(r'^import ([A-Za-z0-9_.]+)$', source.read_text(), re.M)
assert entries[0]['imports'] == ['DiophantineConsistency.NineFreshJones']
assert entries[1]['imports'] == ['DiophantineConsistency.SharingSeed22Dodecic', 'DiophantineConsistency.SharingSign33Squares']
squares = (draft / 'SharingSign22Squares.lean').read_text()
assert 'theorem seed_zero_iff_residuals' in squares and 'SharingSign33Squares.squareSum_zero_iff' in squares
assert digest(packet / 'run.py') == '35af91149ea793952a9ab4670d0da84491665cdff4978cab49a3c321429dc183'
res = subprocess.run([sys.executable, '-I', '-S', '-B', str(packet / 'run.py'), '--preflight'], capture_output=True, text=True, timeout=180)
assert res.returncode == 0 and not res.stderr and json.loads(res.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status': 'PASS_PRELAUNCH', 'residuals_rendered': 13, 'preflight_exit': 0,
                  'runner_sha256': digest(packet / 'run.py'), 'manifest_sha256': digest(manifest),
                  'scope': 'source transcription and no-Lean preflight; no Lean JSON binding or endpoint'}, sort_keys=True, indent=2))
