#!/usr/bin/env python3
"""Generate source-only sign20 forward/reverse zero bridge candidates."""
import hashlib
import json
import sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
here = Path(__file__).resolve().parent
raw = (here.parent / 'nine-sharing-sign20-degree20-e-candidate/seed.json').read_bytes()
assert hashlib.sha256(raw).hexdigest() == '2593aca2ac701ff9312fe5aff1719bbf4fd29a97e2c3e14642bf137d6ef8bf7d'
names = [row['gate'] for row in json.loads(raw)['residuals']]
assert names == ['Y', 'main_root', 'Dc2', 'tau', 'N0', 'Nt',
                 'cTminusR', 'V', 'V2minusY2', 'Na', 'scaled_Ns']
common = '''set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign20ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
'''
oldlist = [f'Sign20Transfers.old{n}' for n in names]
oldlist.insert(1, 'Sign20Coordinate.oldE')
newlist = [f'Sign20Transfers.new{n}' for n in names]
f = '''import DiophantineConsistency.Sign20Transfers00
import DiophantineConsistency.Sign20Transfers01

/-! SOURCE-ONLY forward zero assembly. -/
''' + common + '''
theorem zero_iff_of_eval_eq {σ τ : Type*} (a : Expr σ) (b : Expr τ) (v : σ → V) (w : τ → V)
    (he : a.evalRing (fun i => ι (v i)) = b.evalRing (fun i => ι (w i))) :
    InternalZero a v ↔ InternalZero b w := by
  rw [internalZero_iff, internalZero_iff, he]

theorem old_rows (p : Fin 4 → ℤ) :
    SharingSeed21Degree14.firstResidual p :: SharingSeed21Degree14.remainingResiduals p =
      [''' + ',\n       '.join(x + ' p' for x in oldlist) + '''] := by rfl

theorem forward (p : Fin 4 → ℤ) (beta : V) (v : Fin 21 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed20Degree20.seed p) v) :
    InternalZero (SharingSeed21Degree14.seed p) (Sign20Coordinate.lift beta v) := by
  have hn := (SharingSign20Squares.seed_zero_iff_residuals p v).mp hz
  apply (SharingSign21Squares.seed_zero_iff_residuals p (Sign20Coordinate.lift beta v)).mpr
  intro e he
  rw [old_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with ''' + ' | '.join('rfl' for _ in oldlist) + '\n'
for old_i, row in enumerate(oldlist):
    if old_i == 1:
        f += '  · exact Sign20Coordinate.e_zero p beta v hp0\n'
        continue
    name = names[old_i if old_i < 1 else old_i-1]
    if old_i == 0:
        member = f'by simpa only [Sign20Transfers.new_{name}_row] using hn _ List.mem_cons_self'
    else:
        member = f'hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign20Transfers.new_{name}_row p))))'
    f += f'  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign20Transfers.{name}_eval p beta v hp0)).mpr ({member})\n'
f += 'end DiophantineConsistency.Sign20ZeroBridge\n#print axioms DiophantineConsistency.Sign20ZeroBridge.old_rows\n#print axioms DiophantineConsistency.Sign20ZeroBridge.forward\n'
r = '''import DiophantineConsistency.Sign20ForwardBridge

/-! SOURCE-ONLY reverse zero assembly. -/
''' + common + '''
theorem new_rows (p : Fin 4 → ℤ) :
    SharingSeed20Degree20.firstResidual p :: SharingSeed20Degree20.remainingResiduals p =
      [''' + ',\n       '.join(x + ' p' for x in newlist) + '''] := by rfl

theorem backward (p : Fin 4 → ℤ) (beta : V) (v : Fin 22 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed21Degree14.seed p) v) :
    InternalZero (SharingSeed20Degree20.seed p) (Sign20Coordinate.drop v) := by
  have hz' : InternalZero (SharingSeed21Degree14.seed p)
      (Sign20Coordinate.lift beta (Sign20Coordinate.drop v)) := by
    rw [Sign20Coordinate.lift_drop p beta v hp0 hz]
    exact hz
  have ho := (SharingSign21Squares.seed_zero_iff_residuals p
    (Sign20Coordinate.lift beta (Sign20Coordinate.drop v))).mp hz'
  apply (SharingSign20Squares.seed_zero_iff_residuals p (Sign20Coordinate.drop v)).mpr
  intro e he
  rw [new_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with ''' + ' | '.join('rfl' for _ in newlist) + '\n'
for i, name in enumerate(names):
    if i == 0:
        member = f'by simpa only [Sign20Transfers.old_{name}_row] using ho _ List.mem_cons_self'
    else:
        member = f'ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign20Transfers.old_{name}_row p))))'
    r += f'  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign20Transfers.{name}_eval p beta (Sign20Coordinate.drop v) hp0)).mp ({member})\n'
r += 'end DiophantineConsistency.Sign20ZeroBridge\n#print axioms DiophantineConsistency.Sign20ZeroBridge.new_rows\n#print axioms DiophantineConsistency.Sign20ZeroBridge.backward\n'
for name, source in [('Sign20ForwardBridge.lean', f), ('Sign20ReverseBridge.lean', r)]:
    target = here / name
    if target.exists(): raise SystemExit('refusing to overwrite ' + name)
    target.write_text(source)
print('GENERATED_SOURCE_ONLY old 12/new 11 rows; Lean untested')
