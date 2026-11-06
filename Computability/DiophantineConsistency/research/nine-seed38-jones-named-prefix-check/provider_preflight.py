#!/usr/bin/env python3
"""Recheck exact recipe/cuts producers and mechanical split; no Lean."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
P = Path(__file__).resolve().parent
D = P.parents[1]
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
audits = (
    ('nine-seed38-jones-compact-recipe-terminal-frontier-independent', '1ed31a4f69b3f22cfef198481866e4917cd4785fa0ba9d025551b2d860a9778f', '333840041f59cdb95b8c85e07cd25d2a3448a14e4fee2a5a267c6e2ca3e4f46a'),
    ('nine-seed38-jones-compact-semantics-cut-terminal-frontier-independent', '07982eeff551c60200f490bd36a36781c6630cc791739974c9ec3fba7e1339db', '93813e1c820304ff903147c035c6a5ed50cd4f87bfd9d64e24330700454f1af5'),
)
for name, script_pin, result_pin in audits:
    q = D / 'reviews' / name
    if sha(q / 'check.py') != script_pin or sha(q / 'result.json') != result_pin:
        raise RuntimeError(('audit pin mismatch', name))
    r = subprocess.run([sys.executable, '-I', '-S', '-B', str(q / 'check.py')], capture_output=True, timeout=300)
    if r.returncode or r.stderr or r.stdout != (q / 'result.json').read_bytes():
        raise RuntimeError(('audit failed', name, r.returncode, r.stderr.decode(errors='replace')))
draft = D / 'research/nine-seed38-jones-named-prefix-draft'
if sha(draft / 'split.py') != '8902e2c1d6186159caa679a0fca6e907e5482843874ddb47413299480bd7e775' or sha(draft / 'Norm38MacroPrefixes.lean') != 'c2d995fcf0287325efcfbd060bed17eefd33a1b481a2b67a20978234614b00fa' or sha(draft / 'Norm38MacroPrefixFirst.lean') != 'cad3163594121c4c2d9a626385f1cea9faa3917783510e84a6cf53f0901ba007':
    raise RuntimeError('source pin')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(draft / 'split.py'), '--check'], capture_output=True, timeout=30)
if r.returncode or r.stderr or json.loads(r.stdout)['status'] != 'PASS_MECHANICAL_PREFIX_SPLIT_ONLY':
    raise RuntimeError(('split check', r.returncode, r.stderr.decode(errors='replace')))
base = Path('/tmp/nine-seed38-jones-compact-recipe-check-20261106/lib/DiophantineConsistency')
cuts = Path('/tmp/nine-seed38-jones-compact-semantics-cut-check-20261106/lib/DiophantineConsistency/Norm38MacroCuts.olean')
recipe = base / 'Norm38MacroRecipe.olean'
if not recipe.is_file() or sha(recipe) != 'c1c8213d2c752991e7404820521fcd6466511b187a0648c000894254f4bd7129':
    raise RuntimeError('recipe producer')
if not cuts.is_file() or sha(cuts) != '9c83339175c439edd66ef5a10e6a192b79621803463dbf9e8420fc6f8725bf36':
    raise RuntimeError('cuts producer')
if os.path.lexists(base / 'Norm38MacroCuts.olean'):
    raise RuntimeError('cuts collision in base')
print(json.dumps({'status': 'PASS_POINT_IN_TIME_PROVIDER_SURVEY',
                  'selected': {
                      'DiophantineConsistency.Norm38MacroRecipe': {'realpath': str(recipe.resolve()), 'sha256': sha(recipe)},
                      'DiophantineConsistency.Norm38MacroCuts': {'realpath': str(cuts.resolve()), 'sha256': sha(cuts)}},
                  'scope': 'Audited recipe/cuts producers and textual split only; no Lean, full evaluator identity, JSON proof or complete dynamic ancestry.'}, indent=2, sort_keys=True))
