import OwnZeroProduct74
import FactorResidues74

/-! Source-only composition of the 74 own-zero product and its three literal
mod-four exclusions. Imported source drafts remain unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.OwnZeroUnits74Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open ArithmeticAdaptiveFactorMagnitude2011
open OwnZeroProduct74Draft FactorResidues74Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The 74 own zero makes its guard signed pair the positive unit. -/
theorem guard_pair_unit (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hbeta : (p 0 : DiffRing V)=ι beta) (hb : 0<beta)
    (hJ : 0<v 0) (hw : 0<v 6) (hs : 0<v 7)
    (hz : InternalZero (P74PositiveGuard.graph p).output v) :
    (pairEval (P74PositiveGuard.graph p).guardFactor v).1=
      (pairEval (P74PositiveGuard.graph p).guardFactor v).2+1 := by
  obtain ⟨hmain,haux,hstrong⟩ := restricted_residues p v
  have h := factor_units_of_zero p beta v hbeta hb hJ hw hs hz hmain haux hstrong
  exact h.2.2.2.1

/-- A signed pair is the positive unit exactly when its ring value is one. -/
theorem unit_iff_one {σ : Type*} (e : Expr σ) (v : σ → V) :
    (pairEval e v).1=(pairEval e v).2+1 ↔ e.evalRing (fun j => ι (v j))=1 := by
  rw [← split_evalRing, ← evalSemiring_map ι, ← evalSemiring_map ι, sub_eq_iff_eq_add,
    ← map_one ι, ← map_add, ι_injective.eq_iff, add_comm 1]
  rfl

theorem guard_factor_one (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hbeta : (p 0 : DiffRing V)=ι beta) (hb : 0<beta)
    (hJ : 0<v 0) (hw : 0<v 6) (hs : 0<v 7)
    (hz : InternalZero (P74PositiveGuard.graph p).output v) :
    (P74PositiveGuard.graph p).guardFactor.evalRing (fun j => ι (v j))=1 := by
  exact (unit_iff_one _ v).mp (guard_pair_unit p beta v hbeta hb hJ hw hs hz)

end DiophantineConsistency.OwnZeroUnits74Draft

#print axioms DiophantineConsistency.OwnZeroUnits74Draft.guard_factor_one
