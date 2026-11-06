#!/usr/bin/env python3
"""Generate a finite chain of generic snoc-preservation uses; no Lean."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
P = Path(__file__).resolve().parent
D = P.parent.parent
source = D / 'research/nine-seed38-jones-named-prefix-draft/Norm38MacroPrefixes.lean'
if hashlib.sha256(source.read_bytes()).hexdigest() != 'c2d995fcf0287325efcfbd060bed17eefd33a1b481a2b67a20978234614b00fa':
    raise RuntimeError('prefix source pin')
lines = [
    'import DiophantineConsistency.Norm38MacroPrefixFirst',
    '', '/-! Source-only candidate chain: no semantic theorem is claimed yet. -/',
    'set_option autoImplicit false', 'noncomputable section',
    'namespace DiophantineConsistency.Norm38FirstPreservation',
    'open Norm38MacroLanguage Norm38MacroPrefixes ExecutableJones', '',
    'theorem d45_first_eq_d1 {R : Type*} [CommRing R] (a : Fin 9 → R) :',
    '    d45.values a ⟨0, by decide⟩ = d1.values a ⟨0, by decide⟩ := by',
    '  calc',
]
for n in range(45, 1, -1):
    left = f'd{n}.values a ⟨0, by decide⟩' if n == 45 else '_'
    lines += [
        f'    {left} = d{n - 1}.values a ⟨0, by decide⟩ := by',
        f'      change (Dag.snoc d{n - 1} _).values a (Fin.castSucc ⟨0, by decide⟩) = _',
        f'      exact Norm38MacroCuts.snoc_previous a d{n - 1} _ ⟨0, by decide⟩',
    ]
lines += [
    '', 'theorem recipe_first_value {R : Type*} [CommRing R] (a : Fin 9 → R) :',
    '    Norm38MacroRecipe.recipe.values a ⟨0, by decide⟩ =',
    '      ((indexY Norm38MacroLanguage.seed 0 : Nat) : R) + ((1 : Int) : R) + a ⟨0, by decide⟩ := by',
    '  rw [Norm38MacroPrefixes.recipe_eq_named, d45_first_eq_d1]',
    '  exact Norm38MacroPrefixFirst.first_prefix_value a', '',
    '#print axioms d45_first_eq_d1', '#print axioms recipe_first_value',
    'end DiophantineConsistency.Norm38FirstPreservation',
]
encoded = ('\n'.join(lines) + '\n').encode()
out = P / 'Norm38FirstPreservation.lean'
if sys.argv[1:] == ['--write']:
    with out.open('xb') as f: f.write(encoded)
elif sys.argv[1:] == ['--check']:
    if out.read_bytes() != encoded: raise RuntimeError('generated source differs')
    print(json.dumps({'status': 'PASS_CHAIN_GENERATION_ONLY', 'steps': 44,
                      'source_sha256': hashlib.sha256(encoded).hexdigest(),
                      'scope': 'No Lean, proof acceptance, semantic equality or JSON binding.'}, sort_keys=True))
else:
    raise SystemExit('expected --write or --check')
