#!/usr/bin/env python3
"""Generate source-only sign22 forward/reverse zero bridge candidates."""
import hashlib
import json
import sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
here = Path(__file__).resolve().parent
raw = (here.parent / 'nine-sharing-sign22-dodecic-ky-candidate/seed.json').read_bytes()
assert hashlib.sha256(raw).hexdigest() == '3746dacafb661a8bab30caee81ec3b2130915a8b31adf8fe3630f6a541574f37'
names = [row['gate'] for row in json.loads(raw)['residuals']]
assert names == ['Y', 'E', 'main_root', 'Dc2', 'tau', 'N0', 'Nt',
                 'cTminusR', 'V', 'normalized_S', 'V2minusY2', 'Na', 'scaled_Ns']
common = '''set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign22ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
'''
oldlist = [f'Sign22Transfers.old{n}' for n in names]
oldlist.insert(2, 'Sign22Coordinate.oldkY')
newlist = [f'Sign22Transfers.new{n}' for n in names]
f = '''import DiophantineConsistency.Sign22Transfers00
import DiophantineConsistency.Sign22Transfers01

/-! SOURCE-ONLY forward zero assembly. -/
''' + common + '''
theorem zero_iff_of_eval_eq {σ τ : Type*} (a : Expr σ) (b : Expr τ) (v : σ → V) (w : τ → V)
    (he : a.evalRing (fun i => ι (v i)) = b.evalRing (fun i => ι (w i))) :
    InternalZero a v ↔ InternalZero b w := by
  rw [internalZero_iff, internalZero_iff, he]

theorem old_rows (p : Fin 4 → ℤ) :
    SharingSeed23Octic.firstResidual p :: SharingSeed23Octic.remainingResiduals p =
      [''' + ',\n       '.join(x + ' p' for x in oldlist) + '''] := by rfl

theorem forward (p : Fin 4 → ℤ) (v : Fin 23 → V)
    (hz : InternalZero (SharingSeed22Dodecic.seed p) v) :
    InternalZero (SharingSeed23Octic.seed p) (Sign22Coordinate.lift v) := by
  have hn := (SharingSign22Squares.seed_zero_iff_residuals p v).mp hz
  apply (SharingSign23Squares.seed_zero_iff_residuals p (Sign22Coordinate.lift v)).mpr
  intro e he
  rw [old_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with ''' + ' | '.join('rfl' for _ in oldlist) + '\n'
for old_i, row in enumerate(oldlist):
    if old_i == 2:
        f += '  · exact Sign22Coordinate.ky_zero p v\n'
        continue
    name = names[old_i if old_i < 2 else old_i-1]
    if old_i == 0:
        member = f'by simpa only [Sign22Transfers.new_{name}_row] using hn _ List.mem_cons_self'
    else:
        member = f'hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign22Transfers.new_{name}_row p))))'
    f += f'  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign22Transfers.{name}_eval p v)).mpr ({member})\n'
f += 'end DiophantineConsistency.Sign22ZeroBridge\n#print axioms DiophantineConsistency.Sign22ZeroBridge.old_rows\n#print axioms DiophantineConsistency.Sign22ZeroBridge.forward\n'
r = '''import DiophantineConsistency.Sign22ForwardBridge

/-! SOURCE-ONLY reverse zero assembly. -/
''' + common + '''
theorem new_rows (p : Fin 4 → ℤ) :
    SharingSeed22Dodecic.firstResidual p :: SharingSeed22Dodecic.remainingResiduals p =
      [''' + ',\n       '.join(x + ' p' for x in newlist) + '''] := by rfl

theorem backward (p : Fin 4 → ℤ) (v : Fin 24 → V)
    (hz : InternalZero (SharingSeed23Octic.seed p) v) :
    InternalZero (SharingSeed22Dodecic.seed p) (Sign22Coordinate.drop v) := by
  have hz' : InternalZero (SharingSeed23Octic.seed p)
      (Sign22Coordinate.lift (Sign22Coordinate.drop v)) := by
    rw [Sign22Coordinate.lift_drop p v hz]
    exact hz
  have ho := (SharingSign23Squares.seed_zero_iff_residuals p
    (Sign22Coordinate.lift (Sign22Coordinate.drop v))).mp hz'
  apply (SharingSign22Squares.seed_zero_iff_residuals p (Sign22Coordinate.drop v)).mpr
  intro e he
  rw [new_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with ''' + ' | '.join('rfl' for _ in newlist) + '\n'
for i, name in enumerate(names):
    if i == 0:
        member = f'by simpa only [Sign22Transfers.old_{name}_row] using ho _ List.mem_cons_self'
    else:
        member = f'ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign22Transfers.old_{name}_row p))))'
    r += f'  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign22Transfers.{name}_eval p (Sign22Coordinate.drop v))).mp ({member})\n'
r += 'end DiophantineConsistency.Sign22ZeroBridge\n#print axioms DiophantineConsistency.Sign22ZeroBridge.new_rows\n#print axioms DiophantineConsistency.Sign22ZeroBridge.backward\n'
for name, source in [('Sign22ForwardBridge.lean', f), ('Sign22ReverseBridge.lean', r)]:
    target = here / name
    if target.exists(): raise SystemExit('refusing to overwrite ' + name)
    target.write_text(source)
print('GENERATED_SOURCE_ONLY old 14/new 13 rows; Lean untested')
