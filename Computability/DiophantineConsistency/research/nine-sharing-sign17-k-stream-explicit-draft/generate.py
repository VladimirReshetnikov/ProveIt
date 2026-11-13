#!/usr/bin/env python3
"""Draft a symbolic K stream expression from audited reversed coefficient blocks."""
import re,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;src=P.parent/'nine-sharing-sign17-k-coefficient-reversed-draft'
blocks={}
for g in range(8):
 s=(src/f'Sign17KCoefficientReversed{g:02d}.lean').read_text()
 for name,literal in re.findall(r'theorem (block\d\d|control) :\s*\(List.ofFn [A-Za-z0-9_.]+\).reverse = (\[[^\]]*\])',s):
  assert name not in blocks;blocks[name]=(literal,f'Sign17KCoefficientReversed{g:02d}.{name}')
assert len(blocks)==17
order=['control']+[f'block{k:02d}' for k in reversed(range(16))]
imports='\n'.join(['import DiophantineConsistency.Sign17KCoefficientDecompose']+[f'import DiophantineConsistency.Sign17KCoefficientReversed{k:02d}' for k in range(8)])
values=' ++ '.join(blocks[x][0] for x in order)
rewrites=', '.join(blocks[x][1] for x in order)
out=f'''{imports}

/-! SOURCE ONLY. Explicit numeric list for the actual symbolic K stream. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign17KStreamExplicit
open CurrentKernel2011

def coefficientsReversed : List ℕ := {values}

theorem reversed_explicit :
    (List.ofFn Sign17KLiteralCoefficients.literal).reverse = coefficientsReversed := by
  rw [Sign17KCoefficientDecompose.coefficient_list_reversed]
  rw [{rewrites}]
  all_goals rfl

theorem coefficient_one : Sign17KLiteralCoefficients.literal ⟨1, by decide⟩ = 30099357829122 := by
  decide +kernel

theorem digits_explicit :
    Nat.digits radix K = Sign17KRadixStream.lowPrefix ++
      (coefficientsReversed.set 984 30099357829123 ++ Sign17KRadixStream.suffix) := by
  rw [Sign17KCanonicalDigits.canonical_digits]
  unfold Sign17KRadixStream.digits
  rw [Sign17KStreamBump.block_as_reverse_set, reversed_explicit, coefficient_one]
  all_goals rfl

end DiophantineConsistency.Sign17KStreamExplicit
#print axioms DiophantineConsistency.Sign17KStreamExplicit.reversed_explicit
#print axioms DiophantineConsistency.Sign17KStreamExplicit.coefficient_one
#print axioms DiophantineConsistency.Sign17KStreamExplicit.digits_explicit
'''
(P/'Sign17KStreamExplicit.lean').write_text(out)
print('SOURCE_ONLY numeric symbolic K stream draft; no Lean or file theorem')
