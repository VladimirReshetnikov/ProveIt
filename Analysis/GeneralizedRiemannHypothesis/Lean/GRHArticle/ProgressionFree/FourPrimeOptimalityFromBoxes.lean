import GRHArticle.ProgressionFree.FourPrimeHighDigitChargeBound
import GRHArticle.ProgressionFree.RankinLowDigitChargeMass

/-!
# From the low box to all four-prime exponents

The finite checked margin on good-high slices covers one part of the
admitted nongreedy mass. The explicit ternary tail bound covers the other.
Their combined coefficient is at most one.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators

/-- The full four-coordinate Rankin optimality statement follows from
the finite low-box deficit and the explicit high-digit margin. -/
theorem reciprocalExponentMass_fourPrimeRankinOptimal_of_boxes (q : Fin 4 → ℚ)
    (hq : ∀ i, 1 < q i) (hMargin : (20:ℚ)/21 + fourPrimeHighDigitTail q ≤ 1)
    {F : Set (Fin 4 → ℕ)} (hF : ThreeAPFree F)
    (hBox : ∀ A : Set (Fin 4 → ℕ), ThreeAPFree A →
      let u := fun i ↦ 1/(q i:ℝ)
      (21:ℝ)/20 * exponentDigitSliceMass u fourPrimeLowDigitDepth (A \ rankinExponentVectors _) 0 ≤
        exponentDigitSliceMass u fourPrimeLowDigitDepth (rankinExponentVectors _ \ A) 0) :
    let u := fun i ↦ 1/(q i:ℝ)
    reciprocalExponentMass u F ≤ reciprocalExponentMass u (rankinExponentVectors (Fin 4)) := by
  let u (i : Fin 4) : ℝ := 1/(q i:ℝ)
  let G := rankinExponentVectors (Fin 4)
  let B := rankinBadHighVectors fourPrimeLowDigitDepth F
  let L := rankinBadLowVectors fourPrimeLowDigitDepth F
  let M := reciprocalExponentMass u (G \ F)
  let w := reciprocalExponentMass u
  have hq₁ (i : Fin 4) : 1 < (q i : ℝ) := by exact_mod_cast hq i
  have hq₀ (i : Fin 4) : 0 < (q i : ℝ) := zero_lt_one.trans (hq₁ i)
  have hu₀ (i : Fin 4) : 0 ≤ u i := div_nonneg zero_le_one (hq₀ i).le
  have hu₁ (i : Fin 4) : u i < 1 := (div_lt_one (hq₀ i)).mpr (hq₁ i)
  have hSummable := summable_reciprocalExponentWeight hu₀ hu₁
  have hM : 0 ≤ M := by
    dsimp only [M]
    rw [reciprocalExponentMass_eq_tsum_subtype]
    exact tsum_nonneg fun _ ↦ reciprocalExponentWeight_nonneg hu₀ _
  have hB : w B ≤ M * (fourPrimeHighDigitTail q : ℝ) :=
    reciprocalExponentMass_fourPrimeBadHigh_le q hq hF
  have hL : (21:ℝ)/20 * w L ≤ M :=
    mul_reciprocalExponentMass_rankinBadLow_le u hu₀ hu₁ fourPrimeLowDigitDepth hF (21/20) hBox
  have hBsub : B ⊆ F \ G := by
    intro a ha
    refine ⟨ha.1,fun hg ↦ ?_⟩
    obtain ⟨i,hi⟩ := ha.2
    exact hi (((mem_greedyExponents_iff_mod_pow_and_div _ _).mp (hg i)).2)
  have hD : w B + w L = w (F \ G) := by
    have h := mass_inter_add_sdiff hSummable (F \ G) B
    rw [Set.inter_eq_right.mpr hBsub] at h
    exact h
  have hBad : w (F \ G) ≤ M := calc
    _ = w B + w L := hD.symm
    _ ≤ M * (fourPrimeHighDigitTail q : ℝ) + M * (20/21) := by
      apply add_le_add hB
      linarith
    _ = M * ((20/21:ℝ) + (fourPrimeHighDigitTail q : ℝ)) := by ring
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left
      (by simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using
        (Rat.cast_mono (K := ℝ) hMargin)) hM
    _ = M := mul_one _
  have hFsplit := mass_inter_add_sdiff hSummable F G
  have hGsplit := mass_inter_add_sdiff hSummable G F
  rw [Set.inter_comm G F] at hGsplit
  change w F ≤ w G
  calc
    w F = w (F ∩ G) + w (F \ G) := hFsplit.symm
    _ ≤ w (F ∩ G) + w (G \ F) := by gcongr
    _ = w G := hGsplit

end GRHArticle.ProgressionFree
