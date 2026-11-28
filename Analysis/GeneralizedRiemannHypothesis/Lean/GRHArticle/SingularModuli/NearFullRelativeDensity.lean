import GRHArticle.SingularModuli.OrderDiscriminantCongruences
import GRHArticle.ProgressionFree.Density
import Mathlib.Data.Nat.Periodic

/-!
# Relative density of the two near-maximal-support congruence families

Count discriminants in order of increasing absolute value. The ratio tends
to 9/13 because the common period has exactly 126 qualifying magnitudes
among its 182 order discriminants.
-/

namespace GRHArticle.SingularModuli

open Filter Topology

private theorem count_period_blocks (P : ℕ → Prop) [DecidablePred P] {d : ℕ}
    (hp : Function.Periodic P d) (k : ℕ) : Nat.count P (d*k) = k * Nat.count P d := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hshift : Nat.count (fun n ↦ P (n+d)) (d*k) = Nat.count P (d*k) := by
      simp only [Nat.count_eq_card_filter_range]
      exact congrArg Finset.card (Finset.filter_congr (fun n _ ↦ (hp n).to_iff))
    rw [Nat.mul_succ, Nat.count_add', hshift, ih, Nat.succ_mul]

/-- Every periodic predicate has its per-period mean as its density in
initial segments. -/
theorem tendsto_periodic_count_div (P : ℕ → Prop) [DecidablePred P] {d : ℕ}
    (hd : 0 < d) (hp : Function.Periodic P d) :
    Tendsto (fun N : ℕ ↦ (Nat.count P N : ℝ)/N) atTop (𝓝 ((Nat.count P d : ℝ)/d)) := by
  let c := Nat.count P d
  have hlo (N : ℕ) : (N/d)*c ≤ Nat.count P N := by
    rw [← count_period_blocks P hp]
    exact Nat.count_monotone P (Nat.mul_div_le N d)
  have hhi (N : ℕ) : Nat.count P N ≤ (N/d+1)*c := by
    rw [← count_period_blocks P hp]
    apply Nat.count_monotone P
    have := Nat.mod_add_div N d
    have := Nat.mod_lt N hd
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hr : Tendsto (fun N : ℕ ↦ ((N/d:ℕ):ℝ)/N) atTop (𝓝 (1/(d:ℝ))) :=
    (ProgressionFree.hasNaturalDensity_dvd d hd).congr fun N ↦ by
      rw [ProgressionFree.densityUpTo, ProgressionFree.countUpTo_dvd d N hd]
  have h₀ := hr.mul_const (c:ℝ)
  have hl : Tendsto (fun N : ℕ ↦ ((N/d:ℕ):ℝ)*(c:ℝ)/N) atTop (𝓝 ((c:ℝ)/d)) := by
    have he : 1/(d:ℝ)*c = (c:ℝ)/d := by ring
    rw [he] at h₀
    exact h₀.congr fun n ↦ by ring
  have herr : Tendsto (fun N : ℕ ↦ (c:ℝ)/N) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop _
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl (by simpa only [add_zero] using hl.add herr)
  · intro n
    have hh := hlo n
    exact div_le_div_of_nonneg_right (by exact_mod_cast hh) (Nat.cast_nonneg n)
  · intro n
    have hh : (Nat.count P n : ℝ) ≤ (((n/d : ℕ):ℝ)+1)*c := by exact_mod_cast hhi n
    calc
      _ ≤ ((((n/d : ℕ):ℝ)+1)*c)/n := div_le_div_of_nonneg_right hh (Nat.cast_nonneg n)
      _ = _ := by dsimp; ring

/-- The subset of the actual order discriminants passing at least one of
the two Legendre-symbol tests has relative density 9/13. -/
theorem nearFull_orderDiscriminant_relativeDensity :
    Tendsto (fun N : ℕ ↦ (Nat.count nearFullDiscriminantIndex N : ℝ) /
      (Nat.count orderDiscriminantIndex N : ℝ)) atTop (𝓝 (9/13 : ℝ)) := by
  have ha := tendsto_periodic_count_div nearFullDiscriminantIndex (by decide : 0 < 364)
    nearFullDiscriminantIndex_periodic
  have hb := tendsto_periodic_count_div orderDiscriminantIndex (by decide : 0 < 364)
    orderDiscriminantIndex_periodic
  rw [nearFullDiscriminantIndex_period_counts.2] at ha
  rw [nearFullDiscriminantIndex_period_counts.1] at hb
  have h := ha.div hb (by norm_num)
  norm_num at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  dsimp
  field_simp

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

/-- Count directly by positive magnitudes carrying a primitive reduced form
and by the two Legendre symbols of their negative discriminants. -/
theorem reducedForms_legendre_relativeDensity :
    Tendsto (fun N : ℕ ↦
      (((Finset.range N).filter fun n ↦ (reducedForms n.succPNat).Nonempty ∧
        (legendreSym 7 (-((n+1:ℕ) : ℤ)) = -1 ∨ legendreSym 13 (-((n+1:ℕ) : ℤ)) = -1)).card : ℝ) /
      (((Finset.range N).filter fun n ↦ (reducedForms n.succPNat).Nonempty).card : ℝ))
      atTop (𝓝 (9/13 : ℝ)) := by
  apply nearFull_orderDiscriminant_relativeDensity.congr
  intro N
  simp only [Nat.count_eq_card_filter_range]
  congr 2
  · exact congrArg _ (Finset.filter_congr fun n _ ↦ nearFullDiscriminantIndex_iff n)
  · exact congrArg _ (Finset.filter_congr fun n _ ↦ by
      rw [reducedForms_nonempty_iff_residue]
      rfl)

end GRHArticle.SingularModuli
