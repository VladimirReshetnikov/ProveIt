import Surreal.Algebra.IntersectiveDetector

/-!
# One polynomial tests every ideal

The algebraic consequences of the detector in `odg:def:thm:idealtest`,
`odg:def:eq:idealtest`, and `odg:def:cor:universal`. Quotients are native
Lean ideal quotients, including the zero ring when the ideal is top.
-/

namespace Surreal.IntersectivePolynomial

noncomputable section

variable {R O : Type*} [CommRing R] [CommRing O]

/-- A polynomial value itself has a certificate, with multiplier one. -/
theorem detects_value (t : R) : Detects (value t) := ⟨1, t, mul_one _⟩

/-- The detector identifies precisely the ideals containing a value of Lambda. -/
theorem exists_value_mem_iff (I : Ideal R) (hdet : ∀ a : R, Detects a ↔ a ∉ I)
    (J : Ideal R) : (∃ t : R, value t ∈ J) ↔ ¬J ≤ I := by
  constructor
  · rintro ⟨t, ht⟩ hJI
    exact ((hdet (value t)).mp (detects_value t)) (hJI ht)
  · intro hJI
    obtain ⟨a, ha, hn⟩ : ∃ a : R, a ∈ J ∧ a ∉ I := by
      by_contra! h
      exact hJI h
    obtain ⟨s, t, he⟩ := (hdet a).mpr hn
    exact ⟨t, he ▸ J.mul_mem_right s ha⟩

/-- A root in the quotient is exactly a value in the ideal, without a properness hypothesis. -/
theorem quotient_root_iff (J : Ideal R) :
    (∃ t : R ⧸ J, value t = 0) ↔ ∃ t : R, value t ∈ J := by
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
theorem quotient_no_root_iff (I : Ideal R) (hdet : ∀ a : R, Detects a ↔ a ∉ I)
    (J : Ideal R) : (∀ t : R ⧸ J, value t ≠ 0) ↔ J ≤ I := by
  have h := not_congr ((quotient_root_iff J).trans (exists_value_mem_iff I hdet J))
  simpa only [not_exists, not_not] using h

/-- The detector kernel is the unique greatest ideal with a root-free quotient. -/
theorem greatest_root_free_ideal (I : Ideal R) (hdet : ∀ a : R, Detects a ↔ a ∉ I) :
    IsGreatest {J : Ideal R | ∀ t : R ⧸ J, value t ≠ 0} I :=
  ⟨(quotient_no_root_iff I hdet I).mpr le_rfl,
    fun J hJ => (quotient_no_root_iff I hdet J).mp hJ⟩

/-- Negating the existential detector gives the universal definition of its ideal. -/
theorem mem_iff_universal (I : Ideal R) (hdet : ∀ a : R, Detects a ↔ a ∉ I) (a : R) :
    a ∈ I ↔ ∀ s t : R, a * s ≠ value t := by
  have h := not_congr (hdet a)
  simpa only [Detects, not_exists, not_not] using h.symm

/-- The universal formula also identifies equality of constant terms. -/
theorem constant_eq_iff_universal (ct : R →+* O)
    (hdet : ∀ a : R, Detects a ↔ ct a ≠ 0) (a b : R) :
    ct a = ct b ↔ ∀ s t : R, (a - b) * s ≠ value t := by
  rw [← sub_eq_zero, ← map_sub]
  exact mem_iff_universal (RingHom.ker ct) hdet (a - b)

end
end Surreal.IntersectivePolynomial
