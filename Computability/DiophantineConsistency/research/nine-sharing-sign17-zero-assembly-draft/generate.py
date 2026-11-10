#!/usr/bin/env python3
"""Generate conditional signed-gap zero assembly source, without checking it."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent;raw=(here.parent/'nine-sharing-sign17-degree96-vdifference-candidate/seed.json').read_bytes();assert hashlib.sha256(raw).hexdigest()=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac';names=[r['gate'] for r in json.loads(raw)['residuals']];assert names==['Dc2','tau','N0','Nt','cTminusR','V','Na','scaled_Ns']
common='''set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
''';old=[f'Sign17Transfers.old{n}' for n in names];old.insert(6,'Sign17Coordinate.oldD');new=[f'Sign17Transfers.new{n}' for n in names];imports='\n'.join(f'import DiophantineConsistency.Sign17Transfer{i:02}' for i in range(8))
f=imports+'''\n\n/-! SOURCE-ONLY conditional forward zero assembly. -/\n'''+common+'''
theorem zero_iff_of_eval_eq {σ τ : Type*} (a : Expr σ) (b : Expr τ) (v : σ → V) (w : τ → V)
    (he : a.evalRing (fun i => ι (v i)) = b.evalRing (fun i => ι (w i))) :
    InternalZero a v ↔ InternalZero b w := by
  rw [internalZero_iff, internalZero_iff, he]

theorem old_rows (p : Fin 4 → ℤ) :
    SharingSeed18Degree94.firstResidual p :: SharingSeed18Degree94.remainingResiduals p =
      ['''+',\n       '.join(x+' p' for x in old)+'''] := by rfl

theorem forward (p : Fin 4 → ℤ) (v : Fin 18 → V) (gap : V)
    (hg : ι gap = (ι (v 13) + 1) * (ι (v 13) + 1) - ι (v 17) * ι (v 17))
    (hz : InternalZero (SharingSeed17Degree96.seed p) v) :
    InternalZero (SharingSeed18Degree94.seed p) (Sign17Coordinate.lift v gap) := by
  have hn := (SharingSign17Squares.seed_zero_iff_residuals p v).mp hz
  apply (SharingSign18Squares.seed_zero_iff_residuals p (Sign17Coordinate.lift v gap)).mpr
  intro e he
  rw [old_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with '''+' | '.join('rfl' for _ in old)+'\n'
for j in range(len(old)):
 if j==6:f+='  · exact Sign17Coordinate.d_zero p v gap hg\n';continue
 i=j if j<6 else j-1;n=names[i]
 member=f'by simpa only [Sign17Transfers.new_{n}_row] using hn _ List.mem_cons_self' if i==0 else f'hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign17Transfers.new_{n}_row p))))'
 f+=f'  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign17Transfers.{n}_eval p v gap hg)).mpr ({member})\n'
f+='end DiophantineConsistency.Sign17ZeroBridge\n#print axioms DiophantineConsistency.Sign17ZeroBridge.old_rows\n#print axioms DiophantineConsistency.Sign17ZeroBridge.forward\n'
r='''import DiophantineConsistency.Sign17ForwardBridge

/-! SOURCE-ONLY reverse zero assembly. -/
'''+common+'''
theorem new_rows (p : Fin 4 → ℤ) :
    SharingSeed17Degree96.firstResidual p :: SharingSeed17Degree96.remainingResiduals p =
      ['''+',\n       '.join(x+' p' for x in new)+'''] := by rfl

theorem backward (p : Fin 4 → ℤ) (v : Fin 19 → V)
    (hz : InternalZero (SharingSeed18Degree94.seed p) v) :
    InternalZero (SharingSeed17Degree96.seed p) (Sign17Coordinate.drop v) := by
  have hg : ι (v 18) = (ι ((Sign17Coordinate.drop v) 13) + 1) * (ι ((Sign17Coordinate.drop v) 13) + 1) -
      ι ((Sign17Coordinate.drop v) 17) * ι ((Sign17Coordinate.drop v) 17) := by
    simpa [Sign17Coordinate.drop] using Sign17Coordinate.old_gap p v hz
  have hz' : InternalZero (SharingSeed18Degree94.seed p)
      (Sign17Coordinate.lift (Sign17Coordinate.drop v) (v 18)) := by
    rw [Sign17Coordinate.lift_drop v]
    exact hz
  have ho := (SharingSign18Squares.seed_zero_iff_residuals p
    (Sign17Coordinate.lift (Sign17Coordinate.drop v) (v 18))).mp hz'
  apply (SharingSign17Squares.seed_zero_iff_residuals p (Sign17Coordinate.drop v)).mpr
  intro e he
  rw [new_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with '''+' | '.join('rfl' for _ in new)+'\n'
for i,n in enumerate(names):
 member=f'by simpa only [Sign17Transfers.old_{n}_row] using ho _ List.mem_cons_self' if i==0 else f'ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign17Transfers.old_{n}_row p))))'
 r+=f'  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign17Transfers.{n}_eval p (Sign17Coordinate.drop v) (v 18) hg)).mp ({member})\n'
r+='end DiophantineConsistency.Sign17ZeroBridge\n#print axioms DiophantineConsistency.Sign17ZeroBridge.new_rows\n#print axioms DiophantineConsistency.Sign17ZeroBridge.backward\n'
for name,source in [('Sign17ForwardBridge.lean',f),('Sign17ReverseBridge.lean',r)]:
 p=here/name
 if p.exists():raise SystemExit('refusing overwrite '+str(p))
 p.write_text(source)
print('GENERATED_SOURCE_ONLY old 9/new 8 rows; Lean untested')
