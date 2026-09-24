import Surreal.Algebra.TailoredIntersectiveDetector

/-!
# Ideal tests for the tailored sextic

The ideal and universal-definition clauses of `odg:def:thm:numberfield`.
Native ideal quotients include the zero ring; no properness hypothesis is
imposed. The polynomial parameters are ordinary natural numerals.
-/

namespace Surreal.TailoredIntersectivePolynomial

noncomputable section

variable {R O : Type*} [CommRing R] [CommRing O]
variable (p q : ℕ)

/-- A polynomial value itself has a certificate, with multiplier one. -/
theorem detects_value (t : R) : Detects p q (value p q t) := ⟨1, t, mul_one _⟩

/-- The detector identifies precisely the ideals containing a value of Lambda. -/
theorem exists_value_mem_iff (I : Ideal R) (hdet : ∀ a : R, Detects p q a ↔ a ∉ I)
    (J : Ideal R) : (∃ t : R, value p q t ∈ J) ↔ ¬J ≤ I := by
  constructor
  · rintro ⟨t, ht⟩ hJI
    exact ((hdet (value p q t)).mp (detects_value p q t)) (hJI ht)
  · intro hJI
    obtain ⟨a, ha, hn⟩ : ∃ a : R, a ∈ J ∧ a ∉ I := by
      by_contra! h
      exact hJI h
    obtain ⟨s, t, he⟩ := (hdet a).mpr hn
    exact ⟨t, he ▸ J.mul_mem_right s ha⟩

/-- A root in the quotient is exactly a value in the ideal, without a properness hypothesis. -/
theorem quotient_root_iff (J : Ideal R) :
    (∃ t : R ⧸ J, value p q t = 0) ↔ ∃ t : R, value p q t ∈ J := by
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
    refine ⟨a, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
    rw [map_value]
    exact ht
  · rintro ⟨t, ht⟩
    refine ⟨Ideal.Quotient.mk J t, ?_⟩
    rw [← map_value]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ht

/-- The quotient has no root precisely for ideals contained in the detector kernel. -/
theorem quotient_no_root_iff (I : Ideal R) (hdet : ∀ a : R, Detects p q a ↔ a ∉ I)
    (J : Ideal R) : (∀ t : R ⧸ J, value p q t ≠ 0) ↔ J ≤ I := by
  have h := not_congr ((quotient_root_iff p q J).trans (exists_value_mem_iff p q I hdet J))
  simpa only [not_exists, not_not] using h

/-- The detector kernel is the unique greatest ideal with a root-free quotient. -/
theorem greatest_root_free_ideal (I : Ideal R) (hdet : ∀ a : R, Detects p q a ↔ a ∉ I) :
    IsGreatest {J : Ideal R | ∀ t : R ⧸ J, value p q t ≠ 0} I :=
  ⟨(quotient_no_root_iff p q I hdet I).mpr le_rfl,
    fun J hJ => (quotient_no_root_iff p q I hdet J).mp hJ⟩

/-- Negating the existential detector gives the universal definition of its ideal. -/
theorem mem_iff_universal (I : Ideal R) (hdet : ∀ a : R, Detects p q a ↔ a ∉ I) (a : R) :
    a ∈ I ↔ ∀ s t : R, a * s ≠ value p q t := by
  have h := not_congr (hdet a)
  simpa only [Detects, not_exists, not_not] using h.symm

/-- The universal formula also identifies equality of constant terms. -/
theorem constant_eq_iff_universal (ct : R →+* O)
    (hdet : ∀ a : R, Detects p q a ↔ ct a ≠ 0) (a b : R) :
    ct a = ct b ↔ ∀ s t : R, (a - b) * s ≠ value p q t := by
  rw [← sub_eq_zero, ← map_sub]
  exact mem_iff_universal p q (RingHom.ker ct) hdet (a - b)

end
end Surreal.TailoredIntersectivePolynomial
