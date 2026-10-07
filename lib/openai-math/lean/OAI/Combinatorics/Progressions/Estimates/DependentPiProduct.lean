/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import Mathlib.MeasureTheory.Constructions.Pi

namespace OAI

section

namespace Erdos3

open MeasureTheory MeasureTheory.Measure MeasurableSpace

def dependentPiProd (I : Type*) (X Y : I → Type*)
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)] :
    (∀ i, X i × Y i) ≃ᵐ ((∀ i, X i) × (∀ i, Y i)) where
  toFun x := (fun i => (x i).1, fun i => (x i).2)
  invFun x i := (x.1 i, x.2 i)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := (Measurable.of_eval (fun index =>
    measurable_fst.comp (measurable_pi_apply index))).prodMk
      (Measurable.of_eval (fun index => measurable_snd.comp (measurable_pi_apply index)))
  measurable_invFun := Measurable.of_eval (fun index =>
    ((measurable_pi_apply index).comp measurable_fst).prodMk
      ((measurable_pi_apply index).comp measurable_snd))

theorem dependentPiProd_measurePreserving {I : Type*} [Fintype I] {X Y : I → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (μ : ∀ i, Measure (X i)) (ν : ∀ i, Measure (Y i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] :
    MeasurePreserving (dependentPiProd I X Y) (Measure.pi (fun i => (μ i).prod (ν i)))
      ((Measure.pi μ).prod (Measure.pi ν)) where
  measurable := (dependentPiProd I X Y).measurable
  map_eq := by
    refine (FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
      ((FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn).prod
        (FiniteSpanningSetsIn.pi fun i => (ν i).toFiniteSpanningSetsIn)) ?_).symm
    · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
      · exact (FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn).isCountablySpanning
      · exact (FiniteSpanningSetsIn.pi fun i => (ν i).toFiniteSpanningSetsIn).isCountablySpanning
    · rintro _ ⟨s, ⟨s, _, rfl⟩, ⟨_, ⟨t, _, rfl⟩, rfl⟩⟩
      rw [MeasurableEquiv.map_apply]
      rw [show (dependentPiProd I X Y) ⁻¹' (Set.univ.pi s ×ˢ Set.univ.pi t) =
          Set.univ.pi (fun i => s i ×ˢ t i) by
        ext x
        simp [dependentPiProd, Set.mem_pi, forall_and]]
      simp_rw [Measure.pi_pi, Measure.prod_prod, Measure.pi_pi, Finset.prod_mul_distrib]

end Erdos3

end

end OAI
