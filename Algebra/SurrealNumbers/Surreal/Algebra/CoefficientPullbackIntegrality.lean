import Surreal.Algebra.CoefficientPullback
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Integral elements in a coefficient pullback

The algebraic constant-term argument in `osq:nm:thm:realslice`.
For a split ring retraction, an element is integral over the coefficient
pullback exactly when its retracted coefficient is integral over the
smaller coefficient ring. Ring-homomorphism predicates avoid competing
algebra structures in the commutative square.
-/

namespace Surreal.CoefficientPullback
noncomputable section

variable {A B C E : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing E]

/-- Integrality in the pullback is tested exactly on the retracted coefficient. -/
theorem integralElem_iff (f : A →+* B) (i : C →+* B) (hi : Function.Injective i)
    (s : B →+* A) (hs : ∀ b, f (s b) = b) (x : A) :
    (subring f i).subtype.IsIntegralElem x ↔ i.IsIntegralElem (f x) := by
  have hf : f.comp (subring f i).subtype = i.comp (retraction f i hi) := by
    ext a
    exact (embedding_retraction f i hi a).symm
  have hsec : s.comp i = (subring f i).subtype.comp (sectionMap f i s hs) := rfl
  constructor
  · intro hx
    have h := hx.map f
    rw [hf] at h
    exact h.of_comp
  · intro hx
    have hc := hx.map s
    rw [hsec] at hc
    have hc' : (subring f i).subtype.IsIntegralElem (s (f x)) := hc.of_comp
    have hy : x - s (f x) ∈ subring f i := by
      change ∃ c, i c = f (x - s (f x))
      exact ⟨0, by rw [map_sub, hs, sub_self, map_zero]⟩
    have hp := (subring f i).subtype.isIntegralElem_map (x := ⟨x - s (f x), hy⟩)
    have h := hc'.add _ hp
    simpa only [Subring.subtype_apply, add_sub_cancel] using h

/-- The same criterion holds after any injective embedding of the support ring into an ambient ring. -/
theorem integralElem_ambient_iff (f : A →+* B) (i : C →+* B) (hi : Function.Injective i)
    (s : B →+* A) (hs : ∀ b, f (s b) = b) (j : A →+* E)
    (hj : Function.Injective j) (x : A) :
    (j.comp (subring f i).subtype).IsIntegralElem (j x) ↔ i.IsIntegralElem (f x) :=
  (RingHom.IsIntegralElem.map_iff hj).trans (integralElem_iff f i hi s hs x)

end
end Surreal.CoefficientPullback
