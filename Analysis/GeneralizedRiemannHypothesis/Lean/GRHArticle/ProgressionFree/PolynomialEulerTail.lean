import GRHArticle.ProgressionFree.PolynomialSearchMoments
import GRHArticle.ProgressionFree.PolynomialRoughDensity

/-!
# Error from excluding square factors beyond the smoothness cutoff

Evaluating the finite smooth Euler product at the inverse square of the
field size gives the squarefree correction factor in the article. Through
degree `T` the smooth Euler product already counts every monic polynomial.
-/

namespace GRHArticle.ProgressionFree

open Polynomial UniqueFactorizationMonoid
open scoped BigOperators Classical

variable (F : Type*) [Field F] [Fintype F]

/-- The factor `v_T` in the lower approximation to the polynomial supremum. -/
noncomputable def polynomialSquarefreeRoughRatio (T : ℕ) : ℝ :=
  let w := (Fintype.card F : ℝ)⁻¹
  (1 - w) / ∏ p ∈ polynomialSmoothPrimes F T, (1 - w ^ (2 * p.natDegree))

/-- The smooth Euler coefficient never exceeds the total monic count, and
equals that count in every degree at most the smoothness cutoff. -/
theorem polynomialSmoothDegreeSeries_coeff_le_total (T n : ℕ) :
    let a := PowerSeries.coeff (R := ℕ) n (polynomialSmoothDegreeSeries F T)
    a ≤ Fintype.card F ^ n ∧ (n ≤ T → a = Fintype.card F ^ n) := by
  dsimp only
  rw [coeff_polynomialSmoothDegreeSeries_eq_card, ← card_monicLayer (F := F)]
  have hs : polynomialSmoothLayer F T n ⊆ monicLayer F n := by
    intro f h
    obtain ⟨hm, hd, _⟩ := mem_polynomialSmoothLayer.mp h
    exact mem_monicLayer.mpr ⟨hm, hd⟩
  refine ⟨Finset.card_le_card hs, fun h ↦ congrArg Finset.card (Finset.Subset.antisymm hs ?_)⟩
  intro f hf
  obtain ⟨hm, hd⟩ := mem_monicLayer.mp hf
  exact mem_polynomialSmoothLayer.mpr ⟨hm, hd, fun p hp ↦
    (natDegree_le_of_dvd (dvd_of_mem_normalizedFactors hp) hm.ne_zero).trans (hd ▸ h)⟩

/-- The first `T+1` matching coefficients give the sharper error bound
`q^(-(T+1))` for the squarefree correction. -/
theorem polynomialSquarefreeRoughRatio_error (T : ℕ) :
    let w := (Fintype.card F : ℝ)⁻¹
    0 ≤ 1 - polynomialSquarefreeRoughRatio F T ∧
      1 - polynomialSquarefreeRoughRatio F T ≤ w^(T+1) := by
  let q := (Fintype.card F : ℝ)
  let w := q⁻¹
  let S := polynomialSmoothPrimes F T
  let H := polynomialSmoothDegreeSeries F T
  have hq : 1 < q := by dsimp [q]; exact_mod_cast Fintype.one_lt_card
  have hq₀ : 0 < q := by linarith
  have hw₀ : 0 < w := inv_pos.mpr hq₀
  have hw : w < 1 := inv_lt_one_of_one_lt₀ hq
  have hz : w^2 < 1 := pow_lt_one₀ hw₀.le hw (by decide)
  have hd (p : Polynomial F) (hp : p ∈ S) : 0 < p.natDegree :=
    (mem_polynomialSmoothPrimes.mp hp).2.1.natDegree_pos
  have hmass := (hasTiltedDegreeMoments_smooth S natDegree hd (sq_nonneg w) hz).mass
  change HasSum (tiltedDegreeTerm H (w^2)) _ at hmass
  have htotal (n : ℕ) : q^n * (w^2)^n = w^n := by
    rw [← mul_pow]
    congr 1
    dsimp [w]
    field_simp
  have hcoeff (n : ℕ) : tiltedDegreeTerm H (w^2) n ≤ w^n ∧
      (n ≤ T → tiltedDegreeTerm H (w^2) n = w^n) := by
    obtain ⟨hle, he⟩ := polynomialSmoothDegreeSeries_coeff_le_total F T n
    rw [← htotal n]
    constructor
    · apply mul_le_mul_of_nonneg_right _ (pow_nonneg (sq_nonneg w) _)
      dsimp [H, q]
      exact_mod_cast hle
    · intro hn
      unfold tiltedDegreeTerm
      congr 1
      dsimp [H, q]
      exact_mod_cast he hn
  have hsum : polynomialSquarefreeRoughRatio F T =
      (1-w) * ∑' n, tiltedDegreeTerm H (w^2) n := by
    rw [hmass.tsum_eq]
    simp only [polynomialSquarefreeRoughRatio, S, q, w, pow_mul, div_eq_mul_inv, one_mul,
      Finset.prod_inv_distrib]
  rw [hsum]
  have hgeom := hasSum_geometric_of_lt_one hw₀.le hw
  have hpos : 0 < 1-w := sub_pos.mpr hw
  have hle := hmass.summable.tsum_le_tsum (fun n ↦ (hcoeff n).1) hgeom.summable
  rw [hgeom.tsum_eq] at hle
  have hlo := hmass.summable.sum_le_tsum (Finset.range (T+1)) (fun n _ ↦
    show 0 ≤ tiltedDegreeTerm H (w^2) n from mul_nonneg (Nat.cast_nonneg _) (by positivity))
  have hpfx : ∑ n ∈ Finset.range (T+1), tiltedDegreeTerm H (w^2) n =
      ∑ n ∈ Finset.range (T+1), w^n :=
    Finset.sum_congr rfl fun n hn ↦ (hcoeff n).2 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
  rw [hpfx] at hlo
  have hmul : (1-w) * (∑ n ∈ Finset.range (T+1), w^n) = 1-w^(T+1) := by
    have h := geom_sum_mul w (T+1)
    linarith only [h]
  have hu := mul_le_mul_of_nonneg_left hle hpos.le
  have hl := mul_le_mul_of_nonneg_left hlo hpos.le
  rw [hmul] at hl
  rw [mul_inv_cancel₀ hpos.ne'] at hu
  constructor <;> linarith

/-- The squarefree-correction bound in the article's normalization. -/
theorem polynomialSquarefreeRoughRatio_article_error (T : ℕ) :
    1 - polynomialSquarefreeRoughRatio F T ≤
      (Fintype.card F : ℝ)⁻¹^T / ((Fintype.card F : ℝ)-1) := by
  have hq : 1 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.one_lt_card
  apply (polynomialSquarefreeRoughRatio_error F T).2.trans
  rw [pow_succ, div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact inv_anti₀ (by linarith) (by linarith)

end GRHArticle.ProgressionFree
