#!/usr/bin/env python3
"""Generate source-only sign18 forward/reverse zero bridge candidates."""
import hashlib
import json
import sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
here = Path(__file__).resolve().parent
raw = (here.parent / 'nine-sharing-sign18-degree94-root-candidate/seed.json').read_bytes()
assert hashlib.sha256(raw).hexdigest() == 'd3fd0a00ed9f803a5c002481dbfb22aafe9a5ba34ac89c90069cefbdcaada3fb'
data = json.loads(raw)
names = [row['gate'] for row in data['residuals']]
assert names == ['Dc2', 'tau', 'N0', 'Nt', 'cTminusR', 'V', 'V2minusY2', 'Na', 'scaled_Ns']
common = '''set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign18ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
'''
oldlist = ['SharingSeed19Degree44.firstResidual'] + [f'Sign18Transfers.old{n}' for n in names]
newlist = [f'Sign18Transfers.new{n}' for n in names]
f = '''import DiophantineConsistency.Sign18Transfer00
import DiophantineConsistency.Sign18Transfer01
import DiophantineConsistency.Sign18Transfer02
import DiophantineConsistency.Sign18Transfer03
import DiophantineConsistency.Sign18Transfer04
import DiophantineConsistency.Sign18Transfer05
import DiophantineConsistency.Sign18Transfer06
import DiophantineConsistency.Sign18Transfer07
import DiophantineConsistency.Sign18Transfer08
/-! SOURCE-ONLY forward zero assembly. -/
''' + common + '''
theorem zero_iff_of_eval_eq {σ τ : Type*} (a : Expr σ) (b : Expr τ) (v : σ → V) (w : τ → V)
    (he : a.evalRing (fun i => ι (v i)) = b.evalRing (fun i => ι (w i))) :
    InternalZero a v ↔ InternalZero b w := by
  rw [internalZero_iff, internalZero_iff, he]

theorem old_rows (p : Fin 4 → ℤ) :
    SharingSeed19Degree44.firstResidual p :: SharingSeed19Degree44.remainingResiduals p =
      [''' + ',\n       '.join(x + ' p' for x in oldlist) + '''] := by rfl

theorem forward (p : Fin 4 → ℤ) (beta : V) (v : Fin 19 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed18Degree94.seed p) v) :
    InternalZero (SharingSeed19Degree44.seed p) (Sign18Coordinate.lift beta v) := by
  have hn := (SharingSign18Squares.seed_zero_iff_residuals p v).mp hz
  apply (SharingSign19Squares.seed_zero_iff_residuals p (Sign18Coordinate.lift beta v)).mpr
  intro e he
  rw [old_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with ''' + ' | '.join('rfl' for _ in oldlist) + '''
  · exact Sign18Coordinate.root_zero p beta v hp0
'''
for i, name in enumerate(names):
    if i == 0:
        member = f'by simpa only [Sign18Transfers.new_{name}_row] using hn _ List.mem_cons_self'
    else:
        member = f'hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign18Transfers.new_{name}_row p))))'
    f += f'  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign18Transfers.{name}_eval p beta v hp0)).mpr ({member})\n'
f += 'end DiophantineConsistency.Sign18ZeroBridge\n#print axioms DiophantineConsistency.Sign18ZeroBridge.old_rows\n#print axioms DiophantineConsistency.Sign18ZeroBridge.forward\n'
r = '''import DiophantineConsistency.Sign18ForwardBridge

/-! SOURCE-ONLY reverse zero assembly. -/
''' + common + '''
theorem new_rows (p : Fin 4 → ℤ) :
    SharingSeed18Degree94.firstResidual p :: SharingSeed18Degree94.remainingResiduals p =
      [''' + ',\n       '.join(x + ' p' for x in newlist) + '''] := by rfl

theorem backward (p : Fin 4 → ℤ) (beta : V) (v : Fin 20 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed19Degree44.seed p) v) :
    InternalZero (SharingSeed18Degree94.seed p) (Sign18Coordinate.drop v) := by
  have hz' : InternalZero (SharingSeed19Degree44.seed p)
      (Sign18Coordinate.lift beta (Sign18Coordinate.drop v)) := by
    rw [Sign18Coordinate.lift_drop p beta v hp0 hz]
    exact hz
  have ho := (SharingSign19Squares.seed_zero_iff_residuals p
    (Sign18Coordinate.lift beta (Sign18Coordinate.drop v))).mp hz'
  apply (SharingSign18Squares.seed_zero_iff_residuals p (Sign18Coordinate.drop v)).mpr
  intro e he
  rw [new_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with ''' + ' | '.join('rfl' for _ in newlist) + '\n'
for name in names:
    member = f'ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign18Transfers.old_{name}_row p))))'
    r += f'  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign18Transfers.{name}_eval p beta (Sign18Coordinate.drop v) hp0)).mp ({member})\n'
r += 'end DiophantineConsistency.Sign18ZeroBridge\n#print axioms DiophantineConsistency.Sign18ZeroBridge.new_rows\n#print axioms DiophantineConsistency.Sign18ZeroBridge.backward\n'
for name, source in [('Sign18ForwardBridge.lean', f), ('Sign18ReverseBridge.lean', r)]:
    target = here / name
    if target.exists(): raise SystemExit('refusing to overwrite ' + name)
    target.write_text(source)
print('GENERATED_SOURCE_ONLY old 10/new 9 rows; Lean untested')
