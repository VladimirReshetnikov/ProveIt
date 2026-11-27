import GRHArticle.ProgressionFree.Density
import GRHArticle.ProgressionFree.IntegerPrefix
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Extremal natural and upper densities for integer geometric progressions
-/

namespace GRHArticle.ProgressionFree

open Filter Topology

theorem countUpTo_le_cutoff (A : Set ℕ) (N : ℕ) : countUpTo A N ≤ N := by
  classical
  unfold countUpTo
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using
    Finset.card_filter_le (s := Finset.Icc 1 N) (p := (· ∈ A))

theorem densityUpTo_nonneg (A : Set ℕ) (N : ℕ) : 0 ≤ densityUpTo A N := by
  unfold densityUpTo
  positivity

theorem densityUpTo_le_one (A : Set ℕ) (N : ℕ) : densityUpTo A N ≤ 1 := by
  unfold densityUpTo
  by_cases hN : N = 0
  · simp [hN]
  · have hn : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
    apply (div_le_iff₀ hn).mpr
    rw [one_mul]
    exact_mod_cast countUpTo_le_cutoff A N

theorem hasNaturalDensity_empty : HasNaturalDensity (∅ : Set ℕ) 0 := by
  have hz : densityUpTo (∅ : Set ℕ) = fun _ ↦ 0 := by
    funext N
    simp [densityUpTo, countUpTo]
  rw [HasNaturalDensity, hz]
  exact tendsto_const_nhds

/-- Upper natural density, using the same positive-integer counts as natural
density. -/
noncomputable def integerUpperDensity (A : Set ℕ) : ℝ :=
  limsup (densityUpTo A) atTop

/-- The supremum of the natural densities attained by admissible positive
integer sets. -/
noncomputable def integerNaturalDensitySupremum (integral : Bool) : ℝ :=
  sSup {d : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ IntegerPrefixAdmissible integral A ∧ HasNaturalDensity A d}

/-- The supremum of upper densities attained by admissible positive integer
sets. -/
noncomputable def integerUpperDensitySupremum (integral : Bool) : ℝ :=
  sSup {d : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ IntegerPrefixAdmissible integral A ∧ d = integerUpperDensity A}

theorem naturalDensity_le_one {A : Set ℕ} {d : ℝ} (hd : HasNaturalDensity A d) :
    d ≤ 1 := le_of_tendsto hd (Eventually.of_forall (densityUpTo_le_one A))

theorem integerUpperDensity_le_one (A : Set ℕ) : integerUpperDensity A ≤ 1 := by
  apply limsup_le_of_le _ (Eventually.of_forall (densityUpTo_le_one A))
  exact (isBoundedUnder_of_eventually_ge (Eventually.of_forall (densityUpTo_nonneg A))).isCoboundedUnder_le

theorem integerUpperDensity_eq_of_hasNaturalDensity {A : Set ℕ} {d : ℝ}
    (hd : HasNaturalDensity A d) : integerUpperDensity A = d :=
  Filter.Tendsto.limsup_eq hd

theorem le_integerNaturalDensitySupremum {integral : Bool} {A : Set ℕ} {d : ℝ}
    (h0 : 0 ∉ A) (hA : IntegerPrefixAdmissible integral A) (hd : HasNaturalDensity A d) :
    d ≤ integerNaturalDensitySupremum integral := by
  unfold integerNaturalDensitySupremum
  apply le_csSup
  · exact ⟨1, by rintro e ⟨B, _, _, he⟩; exact naturalDensity_le_one he⟩
  · exact ⟨A, h0, hA, hd⟩

theorem le_integerUpperDensitySupremum {integral : Bool} {A : Set ℕ}
    (h0 : 0 ∉ A) (hA : IntegerPrefixAdmissible integral A) :
    integerUpperDensity A ≤ integerUpperDensitySupremum integral := by
  unfold integerUpperDensitySupremum
  apply le_csSup
  · exact ⟨1, by rintro _ ⟨B, _, _, rfl⟩; exact integerUpperDensity_le_one B⟩
  · exact ⟨A, h0, hA, rfl⟩

/-- A convergent lower bound along cutoffs tending to infinity bounds the
upper density from below. -/
theorem le_integerUpperDensity_of_tendsto_le {A : Set ℕ} {cutoff : ℕ → ℕ}
    {f : ℕ → ℝ} {d : ℝ} (hc : Tendsto cutoff atTop atTop)
    (hf : Tendsto f atTop (𝓝 d))
    (hle : ∀ᶠ n in atTop, f n ≤ densityUpTo A (cutoff n)) :
    d ≤ integerUpperDensity A := by
  apply le_limsup_of_le (isBoundedUnder_of_eventually_le (Eventually.of_forall (densityUpTo_le_one A)))
  intro b hb
  apply le_of_tendsto hf
  filter_upwards [hle, hc.eventually hb] with n h₁ h₂
  exact h₁.trans h₂

end GRHArticle.ProgressionFree
