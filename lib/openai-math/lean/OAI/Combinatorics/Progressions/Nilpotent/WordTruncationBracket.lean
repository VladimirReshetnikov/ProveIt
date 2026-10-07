import OAI.Combinatorics.Progressions.Estimates.FreeLieTreeCoefficientBounds

namespace OAI

section

namespace Erdos3

variable {X : Type*}

theorem wordTruncation_eq_zero_iff (s : ℕ) (p : WordPolynomial X) :
    wordTruncation s p = 0 ↔ ∀ w, w.length ≤ s → p.coeff w = 0 := by
  simpa using wordTruncation_eq_iff s p 0

theorem wordTruncation_succ_mul_eq_zero (s : ℕ) (p q : WordPolynomial X)
    (h : wordTruncation s p = 0 ∨ wordTruncation s q = 0) :
    wordTruncation (s + 1) (p * q) = 0 := by
  classical
  apply (wordTruncation_eq_zero_iff _ _).mpr
  intro w hw
  rw [MonoidAlgebra.coeff_mul]
  apply Finset.sum_eq_zero
  intro u hu
  apply Finset.sum_eq_zero
  intro v hv
  have hne : u * v ≠ w := by
    intro he
    have hlen : u.length + v.length ≤ s + 1 := by
      simpa only [← he, FreeSemigroup.length_mul] using hw
    have hu0 : 0 < u.length := by change 0 < u.tail.length + 1; omega
    have hv0 : 0 < v.length := by change 0 < v.tail.length + 1; omega
    rcases h with hp | hq
    · exact (Finsupp.mem_support_iff.mp hu)
        ((wordTruncation_eq_zero_iff s p).mp hp u (by omega))
    · exact (Finsupp.mem_support_iff.mp hv)
        ((wordTruncation_eq_zero_iff s q).mp hq v (by omega))
  simp only [hne, ite_false]

theorem wordTruncation_succ_lie_eq_zero (s : ℕ) (p q : WordPolynomial X)
    (hq : wordTruncation s q = 0) : wordTruncation (s + 1) ⁅p, q⁆ = 0 := by
  rw [wordPolynomial_lie, map_sub, wordTruncation_succ_mul_eq_zero s p q (Or.inr hq),
    wordTruncation_succ_mul_eq_zero s q p (Or.inl hq), sub_self]

theorem freeLieTruncation_zero (p : FreeLieAlgebra ℚ X) : freeLieTruncation 0 p = 0 := by
  apply freeLieWordExpansion_injective
  rw [freeLieTruncation_expansion, map_zero]
  apply (wordTruncation_eq_zero_iff _ _).mpr
  intro w hw
  have : 0 < w.length := by change 0 < w.tail.length + 1; omega
  omega

theorem freeLie_lowerCentralSeries_truncation_zero (s : ℕ) (p : FreeLieAlgebra ℚ X)
    (hp : p ∈ LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s) :
    freeLieTruncation s p = 0 := by
  induction s generalizing p with
  | zero => exact freeLieTruncation_zero p
  | succ s ih =>
    have hsub : (LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) (s + 1)).toSubmodule ≤
        LinearMap.ker (freeLieTruncation (X := X) (s + 1)) := by
      rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span]
      apply Submodule.span_le.mpr
      rintro z ⟨x, y, rfl⟩
      change freeLieTruncation (s + 1) ⁅x.val, y.val⁆ = 0
      apply freeLieWordExpansion_injective
      rw [freeLieTruncation_expansion, map_zero, LieHom.map_lie]
      apply wordTruncation_succ_lie_eq_zero
      rw [← freeLieTruncation_expansion, ih y.val y.property, map_zero]
    exact hsub hp

end Erdos3

end

end OAI
