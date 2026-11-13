#!/usr/bin/env python3
"""Generate source-only sign19 forward/reverse zero bridge candidates."""
import hashlib
import json
import sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
here = Path(__file__).resolve().parent
raw = (here.parent / 'nine-sharing-sign19-degree44-y-candidate/seed.json').read_bytes()
assert hashlib.sha256(raw).hexdigest() == '01bae1f7680ce07eb5c041d5ae6a625ead9e79e1c968472521458475a4eb94f1'
data = json.loads(raw)
names = [row['gate'] for row in data['residuals']]
assert names == ['main_root', 'Dc2', 'tau', 'N0', 'Nt', 'cTminusR', 'V', 'V2minusY2', 'Na', 'scaled_Ns']
common = '''set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign19ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
'''
oldlist = ['SharingSeed20Degree20.firstResidual'] + [f'Sign19Transfers.old{n}' for n in names]
newlist = [f'Sign19Transfers.new{n}' for n in names]
f = '''import DiophantineConsistency.Sign19Transfers00
import DiophantineConsistency.Sign19Transfers01
/-! SOURCE-ONLY forward zero assembly. -/
''' + common + '''
theorem zero_iff_of_eval_eq {σ τ : Type*} (a : Expr σ) (b : Expr τ) (v : σ → V) (w : τ → V)
    (he : a.evalRing (fun i => ι (v i)) = b.evalRing (fun i => ι (w i))) :
    InternalZero a v ↔ InternalZero b w := by
  rw [internalZero_iff, internalZero_iff, he]

theorem old_rows (p : Fin 4 → ℤ) :
    SharingSeed20Degree20.firstResidual p :: SharingSeed20Degree20.remainingResiduals p =
      [''' + ',\n       '.join(x + ' p' for x in oldlist) + '''] := by rfl

theorem forward (p : Fin 4 → ℤ) (beta : V) (v : Fin 20 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed19Degree44.seed p) v) :
    InternalZero (SharingSeed20Degree20.seed p) (Sign19Coordinate.lift beta v) := by
  have hn := (SharingSign19Squares.seed_zero_iff_residuals p v).mp hz
  apply (SharingSign20Squares.seed_zero_iff_residuals p (Sign19Coordinate.lift beta v)).mpr
  intro e he
  rw [old_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with ''' + ' | '.join('rfl' for _ in oldlist) + '''
  · exact Sign19Coordinate.y_zero p beta v hp0
'''
for i, name in enumerate(names):
    if i == 0:
        member = f'by simpa only [Sign19Transfers.new_{name}_row] using hn _ List.mem_cons_self'
    else:
        member = f'hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign19Transfers.new_{name}_row p))))'
    f += f'  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign19Transfers.{name}_eval p beta v hp0)).mpr ({member})\n'
f += 'end DiophantineConsistency.Sign19ZeroBridge\n#print axioms DiophantineConsistency.Sign19ZeroBridge.old_rows\n#print axioms DiophantineConsistency.Sign19ZeroBridge.forward\n'
r = '''import DiophantineConsistency.Sign19ForwardBridge

/-! SOURCE-ONLY reverse zero assembly. -/
''' + common + '''
theorem new_rows (p : Fin 4 → ℤ) :
    SharingSeed19Degree44.firstResidual p :: SharingSeed19Degree44.remainingResiduals p =
      [''' + ',\n       '.join(x + ' p' for x in newlist) + '''] := by rfl

theorem backward (p : Fin 4 → ℤ) (beta : V) (v : Fin 21 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed20Degree20.seed p) v) :
    InternalZero (SharingSeed19Degree44.seed p) (Sign19Coordinate.drop v) := by
  have hz' : InternalZero (SharingSeed20Degree20.seed p)
      (Sign19Coordinate.lift beta (Sign19Coordinate.drop v)) := by
    rw [Sign19Coordinate.lift_drop p beta v hp0 hz]
    exact hz
  have ho := (SharingSign20Squares.seed_zero_iff_residuals p
    (Sign19Coordinate.lift beta (Sign19Coordinate.drop v))).mp hz'
  apply (SharingSign19Squares.seed_zero_iff_residuals p (Sign19Coordinate.drop v)).mpr
  intro e he
  rw [new_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with ''' + ' | '.join('rfl' for _ in newlist) + '\n'
for name in names:
    member = f'ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign19Transfers.old_{name}_row p))))'
    r += f'  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign19Transfers.{name}_eval p beta (Sign19Coordinate.drop v) hp0)).mp ({member})\n'
r += 'end DiophantineConsistency.Sign19ZeroBridge\n#print axioms DiophantineConsistency.Sign19ZeroBridge.new_rows\n#print axioms DiophantineConsistency.Sign19ZeroBridge.backward\n'
for name, source in [('Sign19ForwardBridge.lean', f), ('Sign19ReverseBridge.lean', r)]:
    target = here / name
    if target.exists(): raise SystemExit('refusing to overwrite ' + name)
    target.write_text(source)
print('GENERATED_SOURCE_ONLY old 11/new 10 rows; Lean untested')
