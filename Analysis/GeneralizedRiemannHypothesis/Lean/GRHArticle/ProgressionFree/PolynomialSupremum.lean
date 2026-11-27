import GRHArticle.ProgressionFree.PolynomialDensitySupremum

/-!
# Attainment of the polynomial progression-free upper density

Choose progression-free sets with upper densities approaching the supremum,
then sample at sufficiently separated degree cutoffs. The loss from retaining
the top degree layers tends to zero.
-/

namespace GRHArticle.ProgressionFree

open Polynomial Filter Topology

/-- Separated degree blocks preserve the polynomial-ratio condition. -/
theorem polynomialRatioThreeGPFree_blockUnion {F : Type*} [Field F]
    {N : ℕ → ℕ} (hgap : ∀ ⦃i j⦄, i < j → 2 * N i + 2 * j < N j)
    {E : ℕ → Set (Polynomial F)} (hE : ∀ j, PolynomialRatioThreeGPFree (E j)) :
    PolynomialRatioThreeGPFree (polynomialBlockUnion N E) := by
  intro f r hf hr ⟨h₀, h₁, h₂⟩
  have hr₀ : r ≠ 0 := by rintro rfl; simp at hr
  let E₀ (j : ℕ) := E j \ {0}
  have hE₀ (j : ℕ) : (0 : Polynomial F) ∉ E₀ j := fun h ↦ h.2 rfl
  have hfree (j : ℕ) (g s : Polynomial F) (hs : 0 < s.natDegree) :
      ¬ (g ∈ E₀ j ∧ g * s ∈ E₀ j ∧ g * s * s ∈ E₀ j) := by
    rintro ⟨hg, hgs, hgss⟩
    exact hE j g s hg.2 hs ⟨hg.1, hgs.1, hgss.1⟩
  have hmem {g : Polynomial F} (hg : g ≠ 0) (h : g ∈ polynomialBlockUnion N E) :
      g ∈ polynomialBlockUnion N E₀ := by
    obtain ⟨j, hj, h₁, h₂⟩ := h
    exact ⟨j, ⟨hj, hg⟩, h₁, h₂⟩
  exact polynomialBlockUnion_no_ratio_progression hgap E₀ hE₀ hfree f r hr
    ⟨hmem hf h₀, hmem (mul_ne_zero hf hr₀) h₁, hmem (mul_ne_zero (mul_ne_zero hf hr₀) hr₀) h₂⟩

variable {F : Type*} [Field F] [Fintype F]

private theorem exists_frequently_lt_polynomialBallProportion_of_lt_supremum {b : ℝ}
    (hb : b < polynomialRatioDensitySupremum F) :
    ∃ E : Set (Polynomial F), PolynomialRatioThreeGPFree E ∧
      ∃ᶠ n in atTop, b < polynomialBallProportion E n := by
  obtain ⟨_, ⟨E, hE, rfl⟩, h⟩ := exists_lt_of_lt_csSup (s :=
    {d : ℝ | ∃ E : Set (Polynomial F), PolynomialRatioThreeGPFree E ∧
      d = limsup (polynomialBallProportion E) atTop})
      (by exact ⟨_, ∅, by simp [PolynomialRatioThreeGPFree], rfl⟩) hb
  exact ⟨E, hE, frequently_lt_of_lt_limsup
    (isCoboundedUnder_le_of_le atTop (polynomialBallProportion_nonneg E)) h⟩

/-- One progression-free set attains `β_q` in upper degree-ball density. -/
theorem polynomialRatioDensitySupremum_attained (F : Type*) [Field F] [Fintype F] :
    ∃ E : Set (Polynomial F), 0 ∉ E ∧ PolynomialRatioThreeGPFree E ∧
      limsup (polynomialBallProportion E) atTop = polynomialRatioDensitySupremum F := by
  let β := polynomialRatioDensitySupremum F
  let lower (j : ℕ) := β - ((j : ℝ) + 1)⁻¹
  have hlower (j : ℕ) : lower j < β := sub_lt_self _ (by positivity)
  choose E hfree hfreq using fun j : ℕ ↦
    exists_frequently_lt_polynomialBallProportion_of_lt_supremum (F := F) (hlower j)
  choose pick hpick hpickProportion using fun j k : ℕ ↦ frequently_atTop.mp (hfreq j) k
  let N : ℕ → ℕ := Nat.rec (pick 0 1) (fun j n ↦ pick (j+1) (2 * n + 2 * (j+1) + 1))
  have hN₀ : 1 ≤ N 0 := hpick 0 1
  have hstep (j : ℕ) : 2 * N j + 2 * (j+1) < N (j+1) :=
    Nat.lt_of_succ_le (hpick (j+1) (2 * N j + 2 * (j+1) + 1))
  have hN : StrictMono N := strictMono_nat_of_lt_succ (fun j ↦ by have := hstep j; omega)
  have hN_gt (j : ℕ) : j < N j := by
    cases j with
    | zero => exact hN₀
    | succ j => have := hstep j; omega
  have hgap ⦃i j : ℕ⦄ (hij : i < j) : 2 * N i + 2 * j < N j := by
    cases j with
    | zero => omega
    | succ j =>
      have hi := hN.monotone (Nat.le_of_lt_succ hij)
      have := hstep j
      omega
  have hsamples (j : ℕ) : lower j < polynomialBallProportion (E j) (N j) := by
    cases j with
    | zero => exact hpickProportion 0 1
    | succ j => exact hpickProportion (j+1) _
  let U := polynomialBlockUnion N E
  have hU₀ : (0 : Polynomial F) ∉ U := by
    rintro ⟨j, _, hj, _⟩
    exact (hN_gt j).not_ge (by simpa using hj)
  have hU := polynomialRatioThreeGPFree_blockUnion hgap hfree
  refine ⟨U, hU₀, hU, le_antisymm (le_polynomialRatioDensitySupremum hU) ?_⟩
  let z := (Fintype.card F : ℝ)⁻¹
  have hq : 1 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.one_lt_card
  have hz := (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr (by positivity))
    (inv_lt_one_of_one_lt₀ hq)).comp (tendsto_add_atTop_nat 1)
  have hsmall : Tendsto (fun j : ℕ ↦ ((j : ℝ)+1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have htarget : Tendsto (fun j ↦ lower j - z ^ (j+1)) atTop (𝓝 β) := by
    simpa [lower, z] using (tendsto_const_nhds (x := β)).sub hsmall |>.sub hz
  apply le_limsup_of_le ⟨1, eventually_map.mpr (Eventually.of_forall (polynomialBallProportion_le_one U))⟩
  intro b hb
  apply le_of_tendsto htarget
  filter_upwards [hN.tendsto_atTop.eventually hb] with j hj
  exact ((sub_le_sub_right (hsamples j).le _).trans
    (polynomialBlockUnion_proportion N E j (hN_gt j).le)).trans hj

end GRHArticle.ProgressionFree
