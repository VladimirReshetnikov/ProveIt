#!/usr/bin/env python3
"""Quote pinned JSON as typed Lean source; not a verified serializer."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
P = Path(__file__).resolve().parent
Q = P.parent / 'nine-seed33-jones-compact-macro-prototype'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
if sha(Q / 'recipe.json') != '06154f18e49d5ac3ca49add3a9b8bb03717f14590d2ef14f892d04b7dc3a75b3':
    raise RuntimeError('recipe hash')
if sha(Q / 'check_structure.py') != '9b19ba8e228d749ec849e6d13179708d670788d5f069818b47d323821d2e1b26':
    raise RuntimeError('validator hash')
r = subprocess.run([sys.executable, '-I', '-S', '-B', str(Q / 'check_structure.py')], capture_output=True, timeout=20)
if r.returncode or r.stderr or json.loads(r.stdout)['status'] != 'PASS_STRUCTURAL_CHECK_ONLY':
    raise RuntimeError('validator')
recipe = json.loads((Q / 'recipe.json').read_bytes())
indices = {}


def nat(e):
    op = e[0]
    if op == 'lit': return f'(.lit {e[1]})'
    if op == 'index' and e[1] == 'r': return '(.index)'
    if op == 'expo' and e[1] == 'k': return '(.expo)'
    if op in ('add', 'sub', 'mul', 'pow'):
        return f'(.{op} {nat(e[1])} {nat(e[2])})'
    raise ValueError(('bad nat', e))


def term(e):
    op = e[0]
    if op == 'const': return f'(.constant ({e[1]} : Int))'
    if op == 'var': return f'(.input ⟨{e[1]}, by decide⟩)'
    if op == 'ref': return f'(.ref ⟨{indices[e[1]]}, by decide⟩)'
    if op == 'fixed' and e[1] == 'z': return '(.fixedZ)'
    if op == 'fixed' and e[1] == 'y': return '(.fixedY)'
    if op == 'pcoef' and e[1] == 'k': return '(.pcoef)'
    if op in ('add', 'sub', 'mul'):
        return f'(.{op} {term(e[1])} {term(e[2])})'
    if op == 'pow': return f'(.pow {term(e[1])} {nat(e[2])})'
    if op == 'sum_range' and e[1] == 'r': return f'(.sumRange {nat(e[2])} {term(e[3])})'
    if op == 'sum_star' and e[1] == 'k': return f'(.sumStar {term(e[2])})'
    raise ValueError(('bad ring', e))


lines = [
    'import DiophantineConsistency.Sign33MacroLanguage',
    '', '/-! Generated source only; neither target below is proved. -/',
    'set_option autoImplicit false', 'noncomputable section',
    'namespace DiophantineConsistency.Sign33MacroRecipe',
    'open Sign33MacroLanguage', '', 'def recipe : Dag 45 := by',
    '  let d0 : Dag 0 := .nil',
]
for j, row in enumerate(recipe['nodes']):
    encoded = term(row['expr'])
    lines.append(f'  let d{j + 1} : Dag {j + 1} := .snoc d{j} {encoded}')
    indices[row['name']] = j
if len(indices) != 45 or recipe['output'] != 'output' or indices['output'] != 44:
    raise RuntimeError('unexpected output')
lines += [
    '  exact d45', '',
    '/-- Open proposition: the generated graph has no unbound macro indices. -/',
    'def WellScopedTarget : Prop := recipe.scoped = true', '',
    '/-- Open proposition: compact graph evaluation equals the checked endpoint. -/',
    'def SemanticTarget : Prop :=',
    '  ∀ (R : Type) [CommRing R] (a : Fin 9 → R),',
    '    recipe.values a (Fin.last 44) = Sign33IPRAEndpoint.expression.evalRing a', '',
    'end DiophantineConsistency.Sign33MacroRecipe',
]
encoded = ('\n'.join(lines) + '\n').encode()
out = P / 'Sign33MacroRecipe.lean'
if sys.argv[1:] == ['--write']:
    with out.open('xb') as f: f.write(encoded)
elif sys.argv[1:] == ['--check']:
    if out.read_bytes() != encoded: raise RuntimeError('Lean quote differs')
    print(json.dumps({'status': 'PASS_QUOTE_REGENERATION_ONLY', 'recipe_sha256': sha(Q / 'recipe.json'),
                      'lean_source_sha256': hashlib.sha256(encoded).hexdigest(),
                      'scope': 'Unverified translator; no Lean parsing, well-scopedness or semantic theorem.'}, sort_keys=True))
else:
    raise SystemExit('expected --write or --check')
