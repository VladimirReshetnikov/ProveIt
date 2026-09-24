import Surreal.Algebra.SmallIntegralUnits

/-!
# The conductor of an integer part into its normalization

The zero-conductor consequence following `osq:nm:thm:density`.
Unique integer parts force a unit gap, while small integral units
produce explicit elements leaving the integer part after multiplication.
-/

namespace Surreal.NormalizationConductor
noncomputable section

variable {R F : Type*} [CommRing R] [CommRing F] [Algebra R F]

/-- The conductor, as an ideal of the original ring, into its ambient integral closure. -/
def conductor (R F : Type*) [CommRing R] [CommRing F] [Algebra R F] : Ideal R where
  carrier := {a | ∀ x : integralClosure R F, ∃ b : R, algebraMap R F b = algebraMap R F a * x}
  zero_mem' := by intro x; exact ⟨0, by simp⟩
  add_mem' := by
    intro a b ha hb x
    obtain ⟨c, hc⟩ := ha x
    obtain ⟨d, hd⟩ := hb x
    exact ⟨c + d, by rw [map_add, hc, hd, map_add, add_mul]⟩
  smul_mem' := by
    intro a b hb x
    obtain ⟨c, hc⟩ := hb x
    exact ⟨a * c, by simp only [smul_eq_mul, map_mul, hc, mul_assoc]⟩

@[simp] theorem mem_conductor (a : R) : a ∈ conductor R F ↔
    ∀ x : integralClosure R F, ∃ b : R, algebraMap R F b = algebraMap R F a * x := Iff.rfl

section Ordered
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Algebra R K]

/-- Unique floors exclude all original-ring values strictly between zero and one. -/
theorem not_between_zero_one
    (hfloor : ∀ x : K, ∃! a : R, algebraMap R K a ≤ x ∧ x < algebraMap R K a + 1)
    (a : R) : ¬ (0 < algebraMap R K a ∧ algebraMap R K a < 1) := by
  rintro ⟨ha0, ha1⟩
  obtain ⟨b, _, hb⟩ := hfloor (algebraMap R K a)
  have h0 : (0 : R) = b := hb 0 (by simpa using And.intro ha0.le ha1)
  have ha : a = b := hb a ⟨le_rfl, lt_add_one _⟩
  have : a = 0 := ha.trans h0.symm
  simp [this] at ha0

/-- Every nonzero value of an integer part has absolute value at least one. -/
theorem one_le_abs
    (hfloor : ∀ x : K, ∃! a : R, algebraMap R K a ≤ x ∧ x < algebraMap R K a + 1)
    (a : R) (ha : algebraMap R K a ≠ 0) : 1 ≤ |algebraMap R K a| := by
  by_contra! h
  rcases lt_or_gt_of_ne ha with hn | hp
  · apply not_between_zero_one hfloor (-a)
    simpa only [map_neg, neg_pos, abs_of_neg hn] using And.intro hn h
  · exact not_between_zero_one hfloor a ⟨hp, by simpa [abs_of_pos hp] using h⟩

variable [HasNonnegSquareRoots K] [FaithfulSMul R K]

/-- A nonzero original-ring element has an integral-unit multiple outside that ring. -/
theorem exists_unit_multiple_not_mem
    (hfloor : ∀ x : K, ∃! a : R, algebraMap R K a ≤ x ∧ x < algebraMap R K a + 1)
    (a : R) (ha : a ≠ 0) :
    ∃ u : integralClosure R K, IsUnit u ∧
      0 < |algebraMap R K a * (u : K)| ∧ |algebraMap R K a * (u : K)| < 1 ∧
      ¬ ∃ b : R, algebraMap R K b = algebraMap R K a * (u : K) := by
  have haK : algebraMap R K a ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R K)).mpr ha
  have habs : 0 < |algebraMap R K a| := abs_pos.mpr haK
  obtain ⟨u, hu, hu0, hub⟩ := SmallIntegralUnits.exists_small_unit
    (fun x => (hfloor x).exists) (1 / |algebraMap R K a|) (by positivity)
  have hp : 0 < |algebraMap R K a * (u : K)| := abs_pos.mpr (mul_ne_zero haK hu0.ne')
  have hl : |algebraMap R K a * (u : K)| < 1 := by
    rw [abs_mul, abs_of_pos hu0]
    have := (lt_div_iff₀ habs).mp hub
    nlinarith
  refine ⟨u, hu, hp, hl, ?_⟩
  rintro ⟨b, hb⟩
  have hn : algebraMap R K b ≠ 0 := by rw [hb]; exact mul_ne_zero haK hu0.ne'
  have := one_le_abs hfloor b hn
  rw [hb] at this
  exact (not_lt_of_ge this) hl

/-- The conductor of any integer part into its normalization is zero. -/
theorem conductor_eq_bot
    (hfloor : ∀ x : K, ∃! a : R, algebraMap R K a ≤ x ∧ x < algebraMap R K a + 1) :
    conductor R K = ⊥ := by
  apply le_antisymm _ bot_le
  intro a ha
  change a = 0
  by_contra hn
  obtain ⟨u, _, _, _, hu⟩ := exists_unit_multiple_not_mem hfloor a hn
  exact hu (ha u)

end Ordered
end
end Surreal.NormalizationConductor
