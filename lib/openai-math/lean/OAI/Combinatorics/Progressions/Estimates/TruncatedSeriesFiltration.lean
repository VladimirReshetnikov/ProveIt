import OAI.Combinatorics.Progressions.Nilpotent.LieBCHContinuity

namespace OAI

section

namespace Erdos3
variable {A : Type*} [Ring A] [Algebra ℚ A]

noncomputable def truncatedSeriesLayer (s i : ℕ) : Submodule ℚ (TruncatedSeries A s) where
  carrier := {p | ∀ n (hn : n ≤ s), n < i → truncatedSeriesCoeff s n hn p = 0}
  zero_mem' n hn _ := map_zero _
  add_mem' hp hq n hn hi := by rw [map_add, hp n hn hi, hq n hn hi, zero_add]
  smul_mem' r p hp n hn hi := by rw [map_smul, hp n hn hi, smul_zero]

theorem truncatedSeriesLayer_mul {s i j : ℕ} {p q : TruncatedSeries A s}
    (hp : p ∈ truncatedSeriesLayer s i) (hq : q ∈ truncatedSeriesLayer s j) :
    p * q ∈ truncatedSeriesLayer s (i + j) := by
  obtain ⟨f, rfl⟩ := truncatedSeriesMk_surjective s p
  obtain ⟨g, rfl⟩ := truncatedSeriesMk_surjective s q
  intro n hn hij
  change PowerSeries.coeff n (f * g) = 0
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro ab hab
  have he := Finset.mem_antidiagonal.mp hab
  by_cases ha : ab.1 < i
  · change ∀ n (hn : n ≤ s), n < i → PowerSeries.coeff n f = 0 at hp
    rw [hp ab.1 (by omega) ha, zero_mul]
  · change ∀ n (hn : n ≤ s), n < j → PowerSeries.coeff n g = 0 at hq
    rw [hq ab.2 (by omega) (by omega), mul_zero]

noncomputable def truncatedSeriesFiltration (s : ℕ) : NilpotentAlgebraFiltration (TruncatedSeries A s) s where
  layer := truncatedSeriesLayer s
  antitone _ _ hij _ hp n hn hi := hp n hn (lt_of_lt_of_le hi hij)
  zero_eq_top := by ext p; simp [truncatedSeriesLayer]
  mul_mem := truncatedSeriesLayer_mul
  terminal := by
    apply le_antisymm
    · intro p hp
      rw [Submodule.mem_bot]
      apply truncatedSeries_ext
      intro n hn
      rw [map_zero]
      exact hp n hn (Nat.lt_succ_of_le hn)
    · exact bot_le

theorem truncatedSeriesLayer_one {s : ℕ} {p : TruncatedSeries A s} :
    p ∈ truncatedSeriesLayer s 1 ↔ p ∈ truncatedSeriesPositive s := by
  obtain ⟨f, rfl⟩ := truncatedSeriesMk_surjective s p
  constructor
  · intro h
    change PowerSeries.constantCoeff f = 0
    simpa only [truncatedSeriesCoeff_mk, PowerSeries.coeff_zero_eq_constantCoeff] using h 0 (Nat.zero_le s) (by decide)
  · intro h n hn hi
    have hn0 : n = 0 := Nat.lt_one_iff.mp hi
    subst n
    change PowerSeries.coeff 0 f = 0
    rw [PowerSeries.coeff_zero_eq_constantCoeff]
    exact h

end Erdos3

end

end OAI
