#!/usr/bin/env python3
"""Generate source-only sign21 forward/reverse zero bridge candidates."""
import hashlib
import json
import sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
here = Path(__file__).resolve().parent
raw = (here.parent / 'nine-sharing-sign21-degree14-s-candidate/seed.json').read_bytes()
assert hashlib.sha256(raw).hexdigest() == '85ad59859a6ebc62f8a4de250ac7abf3af904601e8f6c9e696351d5247ea6e81'
names = [row['gate'] for row in json.loads(raw)['residuals']]
assert names == ['Y', 'E', 'main_root', 'Dc2', 'tau', 'N0', 'Nt',
                 'cTminusR', 'V', 'V2minusY2', 'Na', 'scaled_Ns']
common = '''set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign21ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
'''
oldlist = [f'Sign21Transfers.old{n}' for n in names]
oldlist.insert(9, 'Sign21Coordinate.oldS')
newlist = [f'Sign21Transfers.new{n}' for n in names]
f = '''import DiophantineConsistency.Sign21Transfers00
import DiophantineConsistency.Sign21Transfers01

/-! SOURCE-ONLY forward zero assembly. -/
''' + common + '''
theorem zero_iff_of_eval_eq {σ τ : Type*} (a : Expr σ) (b : Expr τ) (v : σ → V) (w : τ → V)
    (he : a.evalRing (fun i => ι (v i)) = b.evalRing (fun i => ι (w i))) :
    InternalZero a v ↔ InternalZero b w := by
  rw [internalZero_iff, internalZero_iff, he]

theorem old_rows (p : Fin 4 → ℤ) :
    SharingSeed22Dodecic.firstResidual p :: SharingSeed22Dodecic.remainingResiduals p =
      [''' + ',\n       '.join(x + ' p' for x in oldlist) + '''] := by rfl

theorem forward (p : Fin 4 → ℤ) (v : Fin 22 → V)
    (hz : InternalZero (SharingSeed21Degree14.seed p) v) :
    InternalZero (SharingSeed22Dodecic.seed p) (Sign21Coordinate.lift v) := by
  have hn := (SharingSign21Squares.seed_zero_iff_residuals p v).mp hz
  apply (SharingSign22Squares.seed_zero_iff_residuals p (Sign21Coordinate.lift v)).mpr
  intro e he
  rw [old_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with ''' + ' | '.join('rfl' for _ in oldlist) + '\n'
for old_i, row in enumerate(oldlist):
    if old_i == 9:
        f += '  · exact Sign21Coordinate.s_zero p v\n'
        continue
    name = names[old_i if old_i < 9 else old_i-1]
    if old_i == 0:
        member = f'by simpa only [Sign21Transfers.new_{name}_row] using hn _ List.mem_cons_self'
    else:
        member = f'hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign21Transfers.new_{name}_row p))))'
    f += f'  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign21Transfers.{name}_eval p v)).mpr ({member})\n'
f += 'end DiophantineConsistency.Sign21ZeroBridge\n#print axioms DiophantineConsistency.Sign21ZeroBridge.old_rows\n#print axioms DiophantineConsistency.Sign21ZeroBridge.forward\n'
r = '''import DiophantineConsistency.Sign21ForwardBridge

/-! SOURCE-ONLY reverse zero assembly. -/
''' + common + '''
theorem new_rows (p : Fin 4 → ℤ) :
    SharingSeed21Degree14.firstResidual p :: SharingSeed21Degree14.remainingResiduals p =
      [''' + ',\n       '.join(x + ' p' for x in newlist) + '''] := by rfl

theorem backward (p : Fin 4 → ℤ) (v : Fin 23 → V)
    (hz : InternalZero (SharingSeed22Dodecic.seed p) v) :
    InternalZero (SharingSeed21Degree14.seed p) (Sign21Coordinate.drop v) := by
  have hz' : InternalZero (SharingSeed22Dodecic.seed p)
      (Sign21Coordinate.lift (Sign21Coordinate.drop v)) := by
    rw [Sign21Coordinate.lift_drop p v hz]
    exact hz
  have ho := (SharingSign22Squares.seed_zero_iff_residuals p
    (Sign21Coordinate.lift (Sign21Coordinate.drop v))).mp hz'
  apply (SharingSign21Squares.seed_zero_iff_residuals p (Sign21Coordinate.drop v)).mpr
  intro e he
  rw [new_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with ''' + ' | '.join('rfl' for _ in newlist) + '\n'
for i, name in enumerate(names):
    if i == 0:
        member = f'by simpa only [Sign21Transfers.old_{name}_row] using ho _ List.mem_cons_self'
    else:
        member = f'ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign21Transfers.old_{name}_row p))))'
    r += f'  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign21Transfers.{name}_eval p (Sign21Coordinate.drop v))).mp ({member})\n'
r += 'end DiophantineConsistency.Sign21ZeroBridge\n#print axioms DiophantineConsistency.Sign21ZeroBridge.new_rows\n#print axioms DiophantineConsistency.Sign21ZeroBridge.backward\n'
for name, source in [('Sign21ForwardBridge.lean', f), ('Sign21ReverseBridge.lean', r)]:
    target = here / name
    if target.exists(): raise SystemExit('refusing to overwrite ' + name)
    target.write_text(source)
print('GENERATED_SOURCE_ONLY old 13/new 12 rows; Lean untested')
