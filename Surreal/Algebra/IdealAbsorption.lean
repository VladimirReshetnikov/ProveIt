import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.RingTheory.IntegralClosure.IsIntegral.AlmostIntegral
import Mathlib.RingTheory.Localization.AsSubring

/-!
# Absorbing a generated algebra into an ideal

The algebraic step in `osq:nm:thm:onedenominator`: clearing the small
integer-generated algebra suffices to clear the algebra over the full
coefficient ring. The same denominators establish almost integrality
in intermediate rings, as in `osq:nm:thm:complete`.
-/

namespace Surreal.IdealAbsorption
noncomputable section

variable {R F : Type*} [CommRing R] [CommRing F] [Algebra R F]

/-- Clearing the integer-generated algebra into an ideal clears the whole R-algebra. -/
theorem adjoin (I : Ideal R) (s : Set F) (d : F)
    (h : ∀ x ∈ Algebra.adjoin ℤ s, ∃ z ∈ I, algebraMap R F z = d * x) :
    ∀ x ∈ Algebra.adjoin R s, ∃ z ∈ I, algebraMap R F z = d * x := by
  intro x hx
  change x ∈ (Algebra.adjoin R s).toSubmodule at hx
  rw [Algebra.adjoin_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      exact h x ((Submonoid.closure_le.mpr fun y hy => Algebra.subset_adjoin hy) hx)
  | zero => exact ⟨0, I.zero_mem, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨a, ha, he⟩ := hx
      obtain ⟨b, hb, hf⟩ := hy
      exact ⟨a + b, I.add_mem ha hb, by rw [map_add, he, hf, mul_add]⟩
  | smul a x _ hx =>
      obtain ⟨b, hb, he⟩ := hx
      refine ⟨a * b, I.mul_mem_left a hb, ?_⟩
      rw [map_mul, he, Algebra.smul_def]
      ring

/-- An almost-integral element remains almost integral over any intermediate subalgebra. -/
theorem almostIntegral_intermediate [IsDomain R] [IsDomain F] [FaithfulSMul R F]
    {x : F} (h : IsAlmostIntegral R x) (A : Subalgebra R F) : IsAlmostIntegral A x := by
  obtain ⟨d, hd, h⟩ := h
  refine ⟨algebraMap R A d, mem_nonZeroDivisors_iff_ne_zero.mpr ?_, fun n => ?_⟩
  · intro he
    have he' := congrArg (algebraMap A F) he
    have hd' : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd
    apply hd'
    apply FaithfulSMul.algebraMap_injective R F
    simpa using he'
  · obtain ⟨z, hz⟩ := h n
    refine ⟨algebraMap R A z, ?_⟩
    simpa only [Algebra.smul_def, IsScalarTower.algebraMap_apply R A F] using hz

end
end Surreal.IdealAbsorption
