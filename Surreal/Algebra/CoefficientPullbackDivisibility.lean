import Surreal.Algebra.CoefficientPullback

/-!
# Divisibility by constants in coefficient pullbacks

The algebraic prerequisite for `odg:thm:finitequotients`. A split retraction
onto a field allows division by every nonzero coefficient constant. In the
pullback of a coefficient subring, such divisibility is therefore detected
exactly by the retracted coefficient.
-/

namespace Surreal.CoefficientPullback

noncomputable section

variable {A B C : Type*} [CommRing A] [Field B] [CommRing C]

/-- Divisibility by an embedded nonzero constant is equivalent to divisibility of coefficients. -/
theorem sectionMap_dvd_iff (f : A →+* B) (i : C →+* B) (hi : Function.Injective i)
    (s : B →+* A) (hs : ∀ b, f (s b) = b) (c : C) (hc : i c ≠ 0)
    (x : subring f i) :
    sectionMap f i s hs c ∣ x ↔ c ∣ retraction f i hi x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨retraction f i hi y, by rw [map_mul, retraction_sectionMap]⟩
  · rintro ⟨d, hd⟩
    have hx : f x.val = i c * i d := by
      rw [← embedding_retraction f i hi x, hd, map_mul]
    let y : subring f i := ⟨s (i c)⁻¹ * x.val, by
      change ∃ e : C, i e = f (s (i c)⁻¹ * x.val)
      refine ⟨d, ?_⟩
      rw [map_mul, hs, hx, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]⟩
    refine ⟨y, Subtype.ext ?_⟩
    change x.val = s (i c) * (s (i c)⁻¹ * x.val)
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]

end
end Surreal.CoefficientPullback
