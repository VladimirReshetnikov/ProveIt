#!/usr/bin/env python3
"""Generate source-only sign24 forward/reverse zero bridge candidates."""
import hashlib
import json
import sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
here = Path(__file__).resolve().parent
raw = (here.parent / 'nine-sharing-sign24-octic-q3-candidate/seed.json').read_bytes()
assert hashlib.sha256(raw).hexdigest() == '24a6dcf05b96112cfa332aafe4790a367c44b9a0cc033a74197f92d3520ab865'
data = json.loads(raw)
names = [row['gate'] for row in data['residuals']]
assert names == ['Y', 'E', 'kY', 'Delta', 'main_root', 'Dc2', 'tau', 'N0',
                 'Nt', 'cTminusR', 'V', 'normalized_S', 'V2minusY2', 'Na', 'scaled_Ns']
common = '''set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign24ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
'''
oldlist = ['SharingSeed25Octic.firstResidual'] + [f'Sign24Transfers.old{n}' for n in names]
newlist = [f'Sign24Transfers.new{n}' for n in names]
f = '''import DiophantineConsistency.Sign24Transfers00
import DiophantineConsistency.Sign24Transfers01
import DiophantineConsistency.Sign24Transfers02

/-! SOURCE-ONLY forward zero assembly. -/
''' + common + '''
theorem zero_iff_of_eval_eq {σ τ : Type*} (a : Expr σ) (b : Expr τ) (v : σ → V) (w : τ → V)
    (he : a.evalRing (fun i => ι (v i)) = b.evalRing (fun i => ι (w i))) :
    InternalZero a v ↔ InternalZero b w := by
  rw [internalZero_iff, internalZero_iff, he]

theorem old_rows (p : Fin 4 → ℤ) :
    SharingSeed25Octic.firstResidual p :: SharingSeed25Octic.remainingResiduals p =
      [''' + ',\n       '.join(x + ' p' for x in oldlist) + '''] := by rfl

theorem forward (p : Fin 4 → ℤ) (beta : V) (v : Fin 25 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed24Octic.seed p) v) :
    InternalZero (SharingSeed25Octic.seed p) (Sign24Coordinate.lift beta v) := by
  have hn := (SharingSign24Squares.seed_zero_iff_residuals p v).mp hz
  apply (SharingSign25Squares.seed_zero_iff_residuals p (Sign24Coordinate.lift beta v)).mpr
  intro e he
  rw [old_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with ''' + ' | '.join('rfl' for _ in oldlist) + '''
  · exact Sign24Coordinate.q3_zero p beta v hp0
'''
for i, name in enumerate(names):
    if i == 0:
        member = f'by simpa only [Sign24Transfers.new_{name}_row] using hn _ List.mem_cons_self'
    else:
        member = f'hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.new_{name}_row p))))'
    f += f'  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.{name}_eval p beta v hp0)).mpr ({member})\n'
f += 'end DiophantineConsistency.Sign24ZeroBridge\n#print axioms DiophantineConsistency.Sign24ZeroBridge.old_rows\n#print axioms DiophantineConsistency.Sign24ZeroBridge.forward\n'
r = '''import DiophantineConsistency.Sign24ForwardBridge

/-! SOURCE-ONLY reverse zero assembly. -/
''' + common + '''
theorem new_rows (p : Fin 4 → ℤ) :
    SharingSeed24Octic.firstResidual p :: SharingSeed24Octic.remainingResiduals p =
      [''' + ',\n       '.join(x + ' p' for x in newlist) + '''] := by rfl

theorem backward (p : Fin 4 → ℤ) (beta : V) (v : Fin 26 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed25Octic.seed p) v) :
    InternalZero (SharingSeed24Octic.seed p) (Sign24Coordinate.drop v) := by
  have hz' : InternalZero (SharingSeed25Octic.seed p)
      (Sign24Coordinate.lift beta (Sign24Coordinate.drop v)) := by
    rw [Sign24Coordinate.lift_drop p beta v hp0 hz]
    exact hz
  have ho := (SharingSign25Squares.seed_zero_iff_residuals p
    (Sign24Coordinate.lift beta (Sign24Coordinate.drop v))).mp hz'
  apply (SharingSign24Squares.seed_zero_iff_residuals p (Sign24Coordinate.drop v)).mpr
  intro e he
  rw [new_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with ''' + ' | '.join('rfl' for _ in newlist) + '\n'
for name in names:
    member = f'ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.old_{name}_row p))))'
    r += f'  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.{name}_eval p beta (Sign24Coordinate.drop v) hp0)).mp ({member})\n'
r += 'end DiophantineConsistency.Sign24ZeroBridge\n#print axioms DiophantineConsistency.Sign24ZeroBridge.new_rows\n#print axioms DiophantineConsistency.Sign24ZeroBridge.backward\n'
for name, source in [('Sign24ForwardBridge.lean', f), ('Sign24ReverseBridge.lean', r)]:
    target = here / name
    if target.exists(): raise SystemExit('refusing to overwrite ' + name)
    target.write_text(source)
print('GENERATED_SOURCE_ONLY old 16/new 15 rows; Lean untested')
