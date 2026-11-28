import GRHArticle.ProgressionFree.PolynomialRoughCount
import GRHArticle.ProgressionFree.PolynomialReplacementCount
import GRHArticle.ProgressionFree.PolynomialRoughWeightLimit

/-!
# The upper bound for polynomial progression-free density

Fixing the leading scalar and the monic rough part leaves a smooth factor
with a smaller degree budget. The finite maximum bounds each such class.
-/

namespace GRHArticle.ProgressionFree

open Polynomial UniqueFactorizationMonoid Filter Topology
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F]

private noncomputable def selectedNonzero (E : Set (Polynomial F)) (N : ℕ) :
    Finset (Polynomial F) :=
  (polynomialDegreeLTFinset F (N+1)).filter fun f ↦ f ∈ E ∧ f ≠ 0

private theorem mem_selectedNonzero {E : Set (Polynomial F)} {N : ℕ} {f : Polynomial F} :
    f ∈ selectedNonzero E N ↔ f ∈ E ∧ f ≠ 0 ∧ f.natDegree ≤ N := by
  simp only [selectedNonzero, Finset.mem_filter, mem_polynomialDegreeLTFinset]
  constructor
  · rintro ⟨hd, he, h0⟩
    rw [degree_eq_natDegree h0, Nat.cast_lt, Nat.lt_succ_iff] at hd
    exact ⟨he, h0, hd⟩
  · rintro ⟨he, h0, hd⟩
    refine ⟨?_, he, h0⟩
    rwa [degree_eq_natDegree h0, Nat.cast_lt, Nat.lt_succ_iff]

private noncomputable def classKey (T : ℕ) (f : Polynomial F) : F × Polynomial F :=
  (f.leadingCoeff, polynomialRoughPart T f)

private noncomputable def smoothBudgetLayer (E : Set (Polynomial F)) (T N t : ℕ) :
    Finset (Polynomial F) :=
  (selectedNonzero E N).filter fun f ↦ N - (polynomialRoughPart T f).natDegree = t

/-- A uniform size bound for every smooth subset whose nonzero multiples
by one common polynomial belong to the selected global set. -/
def PolynomialSmoothFiberBound (E : Set (Polynomial F)) (T : ℕ) (M : ℕ → ℕ) : Prop :=
  ∀ t (B : Finset (Polynomial F)) (z : Polynomial F), B ⊆ polynomialSmoothBall F T t →
    (∀ b ∈ B, z*b ≠ 0 ∧ z*b ∈ E) → B.card ≤ M t

theorem PolynomialRatioThreeGPFree.smoothFiberBound {E : Set (Polynomial F)}
    (hE : PolynomialRatioThreeGPFree E) (T : ℕ) :
    PolynomialSmoothFiberBound E T (polynomialSmoothMaximum F T) := by
  intro t B z hB hmul
  apply le_polynomialSmoothMaximum hB
  intro f r _ hr h
  have ha := hmul f h.1
  have hb := hmul _ h.2.1
  have hc := hmul _ h.2.2
  exact hE (z*f) r ha.1 hr ⟨ha.2, by simpa only [mul_assoc] using hb.2,
    by simpa only [mul_assoc] using hc.2⟩

private theorem card_scalar_rough_fiber_le {E : Set (Polynomial F)}
    {M : ℕ → ℕ} {T : ℕ} (hE : PolynomialSmoothFiberBound E T M) (N t : ℕ) (k : F × Polynomial F) :
    ((smoothBudgetLayer E T N t).filter fun f ↦ classKey T f = k).card ≤
      M t := by
  let B := (smoothBudgetLayer E T N t).filter fun f ↦ classKey T f = k
  let H := B.image (polynomialSmoothPart T)
  have hparts (f : Polynomial F) (hf : f ∈ B) :
      C k.1 * k.2 * polynomialSmoothPart T f = f := by
    have hk := (Finset.mem_filter.mp hf).2
    have hc : f.leadingCoeff = k.1 := congrArg Prod.fst hk
    have hg : polynomialRoughPart T f = k.2 := congrArg Prod.snd hk
    rw [← hc, ← hg]
    exact polynomial_eq_leadingCoeff_mul_roughPart_mul_smoothPart T f
  have hbase (f : Polynomial F) (hf : f ∈ B) :
      f ∈ E ∧ f ≠ 0 ∧ f.natDegree ≤ N :=
    mem_selectedNonzero.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).1
  have hcard : H.card = B.card := by
    apply Finset.card_image_of_injOn
    intro f hf g hg he
    rw [← hparts f hf, ← hparts g hg, he]
  have hsub : H ⊆ polynomialSmoothBall F T t := by
    intro h hh
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hh
    obtain ⟨_, hf₀, hfd⟩ := hbase f hf
    have hbudget := (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2
    have hds := natDegree_roughPart_add_smoothPart T hf₀
    refine mem_polynomialSmoothBall.mpr ⟨monic_polynomialSmoothPart T f, by omega, ?_⟩
    rw [normalizedFactors_polynomialSmoothPart]
    exact fun p hp ↦ (Multiset.mem_filter.mp hp).2
  rw [← hcard]
  apply hE t H (C k.1 * k.2) hsub
  intro b hb
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
  rw [hparts f hf]
  exact ⟨(hbase f hf).2.1, (hbase f hf).1⟩

private theorem card_budgetLayer_le {E : Set (Polynomial F)} {M : ℕ → ℕ} {T : ℕ}
    (hE : PolynomialSmoothFiberBound E T M) (N t : ℕ) :
    (smoothBudgetLayer E T N t).card ≤
      (Fintype.card F - 1) * (polynomialRoughLayer F T (N-t)).card *
        M t := by
  let S := (Finset.univ.erase 0 : Finset F) ×ˢ polynomialRoughLayer F T (N-t)
  have hmaps : Set.MapsTo (classKey T) (smoothBudgetLayer E T N t : Set (Polynomial F)) S := by
    intro f hf
    have hf' : f ∈ (selectedNonzero E N).filter (fun f ↦ N - (polynomialRoughPart T f).natDegree = t) := hf
    obtain ⟨hfB, hb⟩ := Finset.mem_filter.mp hf'
    obtain ⟨_, h0, hN⟩ := mem_selectedNonzero.mp hfB
    have hd := natDegree_roughPart_add_smoothPart T h0
    have hrough : (polynomialRoughPart T f).natDegree = N-t := by omega
    change (f.leadingCoeff, polynomialRoughPart T f) ∈ S
    exact Finset.mem_product.mpr ⟨Finset.mem_erase.mpr ⟨leadingCoeff_ne_zero.mpr h0, Finset.mem_univ _⟩,
      mem_polynomialRoughLayer.mpr ⟨monic_polynomialRoughPart T f, hrough, by
        rw [normalizedFactors_polynomialRoughPart, polynomialRoughFactors]
        exact fun p hp ↦ (Multiset.mem_filter.mp hp).2⟩⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hs := Finset.sum_le_sum (s := S) (fun k _ ↦ card_scalar_rough_fiber_le hE N t k)
  simpa only [S, Finset.sum_const, nsmul_eq_mul, Finset.card_product,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Nat.cast_id] using hs

/-- At a finite cutoff, the scalar and rough classes bound the selected count.
The extra `1` accommodates a possible zero polynomial. -/
theorem PolynomialSmoothFiberBound.card_polynomialBall_le {E : Set (Polynomial F)} {T : ℕ} {M : ℕ → ℕ}
    (hE : PolynomialSmoothFiberBound E T M) (N : ℕ) :
    ((polynomialDegreeLTFinset F (N+1)).filter (· ∈ E)).card ≤
      1 + (Fintype.card F - 1) * ∑ t ∈ Finset.range (N+1),
        (polynomialRoughLayer F T (N-t)).card * M t := by
  let B := (polynomialDegreeLTFinset F (N+1)).filter (· ∈ E)
  have hpart := Finset.card_filter_add_card_filter_not (s := B) (fun f ↦ f ≠ 0)
  have hnz : (B.filter fun f ↦ f ≠ 0) = selectedNonzero E N := by
    simp only [B, selectedNonzero, Finset.filter_filter]
  have hzero : (B.filter fun f ↦ ¬ f ≠ 0).card ≤ 1 := by
    have hs : B.filter (fun f ↦ ¬ f ≠ 0) ⊆ {0} := by simp [Finset.subset_iff]
    simpa using Finset.card_le_card hs
  have hm : Set.MapsTo (fun f : Polynomial F ↦ N - (polynomialRoughPart T f).natDegree)
      (selectedNonzero E N : Set (Polynomial F)) (Finset.range (N+1)) :=
    fun f _ ↦ Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le _ _))
  have hb := Finset.card_eq_sum_card_fiberwise hm
  change (selectedNonzero E N).card = ∑ t ∈ Finset.range (N+1), (smoothBudgetLayer E T N t).card at hb
  have hbound := Finset.sum_le_sum (s := Finset.range (N+1)) (fun t _ ↦ card_budgetLayer_le hE N t)
  simp only [mul_assoc, ← Finset.mul_sum] at hbound
  rw [hnz, hb] at hpart
  change B.card ≤ _
  omega

/-- The normalized finite upper bound, grouped by the remaining smooth degree budget. -/
theorem PolynomialSmoothFiberBound.proportion_le_convolution {E : Set (Polynomial F)} {T : ℕ} {M : ℕ → ℕ}
    (hE : PolynomialSmoothFiberBound E T M) (N : ℕ) :
    polynomialBallProportion E N ≤ (Fintype.card F : ℝ)⁻¹^(N+1) +
      (1 - (Fintype.card F : ℝ)⁻¹) *
        ∑ t ∈ Finset.range (N+1),
          ((polynomialRoughLayer F T (N-t)).card / (Fintype.card F : ℝ)^(N-t)) *
            ((M t : ℝ) * (Fintype.card F : ℝ)⁻¹^t) := by
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  let r (n : ℕ) := (polynomialRoughLayer F T n).card
  unfold polynomialBallProportion
  calc
    _ ≤ ((↑(1 + (Fintype.card F - 1) * ∑ t ∈ Finset.range (N+1),
        r (N-t) * M t) : ℝ) / (Fintype.card F : ℝ)^(N+1)) := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hq.le _)
      exact_mod_cast hE.card_polynomialBall_le N
    _ = _ := by
      rw [Nat.cast_add, Nat.cast_one, add_div, polynomial_weighted_convolution_scale F N r M,
        one_div, ← inv_pow]

/-- Every progression-free set has upper density at most `U_T`. -/
theorem PolynomialSmoothFiberBound.limsup_le {E : Set (Polynomial F)} {T : ℕ} {M : ℕ → ℕ}
    (hE : PolynomialSmoothFiberBound E T M)
    (hs : Summable (fun t ↦ (M t : ℝ) * (Fintype.card F : ℝ)⁻¹^t)) :
    limsup (polynomialBallProportion E) atTop ≤ polynomialDensityUpperWith F T M := by
  let q := (Fintype.card F : ℝ)
  let r (n : ℕ) := ((polynomialRoughLayer F T n).card : ℝ) / q^n
  have hq : 1 < q := by
    change 1 < (Fintype.card F : ℝ)
    exact_mod_cast Fintype.one_lt_card
  have hr (n : ℕ) : r n ∈ Set.Icc 0 1 := by
    refine ⟨by dsimp [r,q]; positivity, (div_le_one (pow_pos (by linarith) _)).mpr ?_⟩
    change ((polynomialRoughLayer F T n).card : ℝ) ≤ (Fintype.card F : ℝ)^n
    exact_mod_cast polynomialRoughLayer_card_le_pow (F := F) T n
  have hsum := tendsto_weighted_rough_convolution _ hs (fun _ ↦ by positivity) hr
    (tendsto_polynomialRoughLayer_card_div_pow (F := F) T)
  have hsmall := (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr (by linarith : 0 ≤ q))
    (inv_lt_one_of_one_lt₀ hq)).comp (tendsto_add_atTop_nat 1)
  have hlim : Tendsto (fun N ↦ q⁻¹^(N+1) + (1-q⁻¹) *
      ∑ t ∈ Finset.range (N+1), r (N-t) * ((M t : ℝ) * q⁻¹^t))
      atTop (𝓝 (polynomialDensityUpperWith F T M)) := by
    simpa only [q, Function.comp_apply, polynomialDensityUpperWith, zero_add, mul_assoc] using
      hsmall.add (tendsto_const_nhds.mul hsum : Tendsto (fun N ↦ (1-q⁻¹) * _)
        atTop (𝓝 ((1-q⁻¹) * _)))
  exact (limsup_le_limsup (Eventually.of_forall (hE.proportion_le_convolution))
    (isCoboundedUnder_le_of_le _ (polynomialBallProportion_nonneg E)) hlim.isBoundedUnder_le).trans_eq
    hlim.limsup_eq

theorem card_polynomialBall_le_smoothMaximum {E : Set (Polynomial F)}
    (hE : PolynomialRatioThreeGPFree E) (T N : ℕ) :
    ((polynomialDegreeLTFinset F (N+1)).filter (· ∈ E)).card ≤
      1 + (Fintype.card F - 1) * ∑ t ∈ Finset.range (N+1),
        (polynomialRoughLayer F T (N-t)).card * polynomialSmoothMaximum F T t :=
  (hE.smoothFiberBound T).card_polynomialBall_le N

theorem polynomialBallProportion_le_smoothMaximum_convolution {E : Set (Polynomial F)}
    (hE : PolynomialRatioThreeGPFree E) (T N : ℕ) :
    polynomialBallProportion E N ≤ (Fintype.card F : ℝ)⁻¹^(N+1) +
      (1 - (Fintype.card F : ℝ)⁻¹) *
        ∑ t ∈ Finset.range (N+1),
          ((polynomialRoughLayer F T (N-t)).card / (Fintype.card F : ℝ)^(N-t)) *
            ((polynomialSmoothMaximum F T t : ℝ) * (Fintype.card F : ℝ)⁻¹^t) :=
  (hE.smoothFiberBound T).proportion_le_convolution N

theorem limsup_polynomialBallProportion_le_polynomialDensityUpperApproximation
    {E : Set (Polynomial F)} (hE : PolynomialRatioThreeGPFree E) (T : ℕ) :
    limsup (polynomialBallProportion E) atTop ≤ polynomialDensityUpperApproximation F T :=
  (hE.smoothFiberBound T).limsup_le (summable_polynomialSmoothMaximum_weight (F := F) T)

/-- The upper half `β_q ≤ U_T` of the article's density sandwich. -/
theorem polynomialRatioDensitySupremum_le_polynomialDensityUpperApproximation
    (F : Type*) [Field F] [Fintype F] [decEq : DecidableEq F] (T : ℕ) :
    polynomialRatioDensitySupremum F ≤ polynomialDensityUpperApproximation F T := by
  rw [show decEq = Classical.decEq F from Subsingleton.elim _ _]
  apply csSup_le
  · exact ⟨_, ∅, by simp [PolynomialRatioThreeGPFree], rfl⟩
  · rintro d ⟨E, hE, rfl⟩
    exact limsup_polynomialBallProportion_le_polynomialDensityUpperApproximation hE T

end GRHArticle.ProgressionFree
