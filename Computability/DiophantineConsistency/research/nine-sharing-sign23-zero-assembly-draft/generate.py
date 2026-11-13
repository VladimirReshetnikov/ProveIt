#!/usr/bin/env python3
"""Generate source-only sign23 forward/reverse zero bridge candidates."""
import hashlib
import json
import sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
here = Path(__file__).resolve().parent
raw = (here.parent / 'nine-sharing-sign23-octic-delta-candidate/seed.json').read_bytes()
assert hashlib.sha256(raw).hexdigest() == 'ee6079ea26dd120fab39789f83034947c18e0c8806945a1fc75fca62e1c65d41'
names = [row['gate'] for row in json.loads(raw)['residuals']]
assert names == ['Y', 'E', 'kY', 'main_root', 'Dc2', 'tau', 'N0', 'Nt',
                 'cTminusR', 'V', 'normalized_S', 'V2minusY2', 'Na', 'scaled_Ns']
common = '''set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign23ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
'''
oldlist = [f'Sign23Transfers.old{n}' for n in names]
oldlist.insert(3, 'Sign23Coordinate.oldDelta')
newlist = [f'Sign23Transfers.new{n}' for n in names]
f = '''import DiophantineConsistency.Sign23Transfers00
import DiophantineConsistency.Sign23Transfers01

/-! SOURCE-ONLY forward zero assembly. -/
''' + common + '''
theorem zero_iff_of_eval_eq {σ τ : Type*} (a : Expr σ) (b : Expr τ) (v : σ → V) (w : τ → V)
    (he : a.evalRing (fun i => ι (v i)) = b.evalRing (fun i => ι (w i))) :
    InternalZero a v ↔ InternalZero b w := by
  rw [internalZero_iff, internalZero_iff, he]

theorem old_rows (p : Fin 4 → ℤ) :
    SharingSeed24Octic.firstResidual p :: SharingSeed24Octic.remainingResiduals p =
      [''' + ',\n       '.join(x + ' p' for x in oldlist) + '''] := by rfl

theorem forward (p : Fin 4 → ℤ) (v : Fin 24 → V)
    (hz : InternalZero (SharingSeed23Octic.seed p) v) :
    InternalZero (SharingSeed24Octic.seed p) (Sign23Coordinate.lift v) := by
  have hn := (SharingSign23Squares.seed_zero_iff_residuals p v).mp hz
  apply (SharingSign24Squares.seed_zero_iff_residuals p (Sign23Coordinate.lift v)).mpr
  intro e he
  rw [old_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with ''' + ' | '.join('rfl' for _ in oldlist) + '\n'
for old_i, row in enumerate(oldlist):
    if old_i == 3:
        f += '  · exact Sign23Coordinate.delta_zero p v\n'
        continue
    name = names[old_i if old_i < 3 else old_i-1]
    if old_i == 0:
        member = f'by simpa only [Sign23Transfers.new_{name}_row] using hn _ List.mem_cons_self'
    else:
        member = f'hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign23Transfers.new_{name}_row p))))'
    f += f'  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.{name}_eval p v)).mpr ({member})\n'
f += 'end DiophantineConsistency.Sign23ZeroBridge\n#print axioms DiophantineConsistency.Sign23ZeroBridge.old_rows\n#print axioms DiophantineConsistency.Sign23ZeroBridge.forward\n'
r = '''import DiophantineConsistency.Sign23ForwardBridge

/-! SOURCE-ONLY reverse zero assembly. -/
''' + common + '''
theorem new_rows (p : Fin 4 → ℤ) :
    SharingSeed23Octic.firstResidual p :: SharingSeed23Octic.remainingResiduals p =
      [''' + ',\n       '.join(x + ' p' for x in newlist) + '''] := by rfl

theorem backward (p : Fin 4 → ℤ) (v : Fin 25 → V)
    (hz : InternalZero (SharingSeed24Octic.seed p) v) :
    InternalZero (SharingSeed23Octic.seed p) (Sign23Coordinate.drop v) := by
  have hz' : InternalZero (SharingSeed24Octic.seed p)
      (Sign23Coordinate.lift (Sign23Coordinate.drop v)) := by
    rw [Sign23Coordinate.lift_drop p v hz]
    exact hz
  have ho := (SharingSign24Squares.seed_zero_iff_residuals p
    (Sign23Coordinate.lift (Sign23Coordinate.drop v))).mp hz'
  apply (SharingSign23Squares.seed_zero_iff_residuals p (Sign23Coordinate.drop v)).mpr
  intro e he
  rw [new_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with ''' + ' | '.join('rfl' for _ in newlist) + '\n'
for i, name in enumerate(names):
    if i == 0:
        member = f'by simpa only [Sign23Transfers.old_{name}_row] using ho _ List.mem_cons_self'
    else:
        member = f'ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign23Transfers.old_{name}_row p))))'
    r += f'  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.{name}_eval p (Sign23Coordinate.drop v))).mp ({member})\n'
r += 'end DiophantineConsistency.Sign23ZeroBridge\n#print axioms DiophantineConsistency.Sign23ZeroBridge.new_rows\n#print axioms DiophantineConsistency.Sign23ZeroBridge.backward\n'
for name, source in [('Sign23ForwardBridge.lean', f), ('Sign23ReverseBridge.lean', r)]:
    target = here / name
    if target.exists(): raise SystemExit('refusing to overwrite ' + name)
    target.write_text(source)
print('GENERATED_SOURCE_ONLY old 15/new 14 rows; Lean untested')
