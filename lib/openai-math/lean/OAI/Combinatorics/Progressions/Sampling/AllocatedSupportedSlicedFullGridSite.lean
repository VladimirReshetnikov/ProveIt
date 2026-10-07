import OAI.Combinatorics.Progressions.Dynamics.ScalarSiteCeilScaleBudget
import OAI.Combinatorics.Progressions.Geometry.AllocatedSupportedSlicedNaturalSiteError

namespace OAI

section

namespace Erdos3.VectorPolynomial

universe uα

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "denom" => inactiveDenominator gamma
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "torusA" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)
local notation "torusI" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

include hq in
theorem exists_allocatedSupportedSliced_mixed_grid_site_expansion
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j,Sum.inr i⟩)
    {δ : ℝ} (hδ : 0 < δ)
    (hdense : ∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ ≤
      (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (T : ℕ) (hQT : (((Fintype.card α + 1) * q : ℕ) : ℝ) / δ ≤ T)
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hBa : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hσ1 : σ j ≤ 1) :
    let d := rows.card
    let ta := (layerTailDegree m + 1) * d
    let ti := degree * d
    let Va := ((torusA : ℝ) / (2 * gamma)) / δ ^ degree
    let Vi := (torusI : ℝ) * cost / δ ^ degree
    let Wa := (torusA : ℝ) ^ d / δ ^ ta
    let Wi := ((torusI : ℝ) * cost) ^ d / δ ^ ti
    let ζa := positiveModerateRetainedBias j.val d ta P Va Wa ε
    let ζi := uniformBlockRetainedBias j.val d ti P Vi Wi ε
    let fa := Real.toNNReal (positiveRetainedFrequencyBound j.val d P Va ζa)
    let fi := Real.toNNReal (uniformScaledRetainedFrequencyBound j.val d P Vi ζi)
    let ca := positiveModerateSpectrumCardBudget j.val d ta P Va Wa 1 + 1
    let ci := uniformSpectrumAbsoluteCap j.val d ti P Vi Wi
    let Kmax := allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i T
    let R0 := (d : ℝ) *
      ((Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) * R j)
    ∀ {Q : ℝ}, 0 ≤ Q → R0 + 1 / 4 ≤ Real.exp Q →
      (ε / (ca + 1))⁻¹ ≤ Real.exp Q → (ε / (ci + 1))⁻¹ ≤ Real.exp Q →
      ((CircleFourier.characterLipConstant * (d * fa) + 4) * (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q →
      ((CircleFourier.characterLipConstant * (d * fi) + 4) * (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q →
      (Kmax : ℝ) ^ d ≤ Real.exp Q →
      ((d * (2 * (Kmax : ℝ≥0) ^ 2) * (Kmax : ℝ≥0) ^ d) * (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q →
      ε⁻¹ ≤ Real.exp Q →
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds
        (max 1 (max (positiveModerateSpectrumCardBudget j.val d ta P Va Wa ε)
          (uniformSpectrumSizeConstant j.val d ti P Vi Wi /
            ε ^ max (majorArcSpectrumExponent j.val d) (majorArcLengthExponent j.val * ti))) *
          Real.exp (Fintype.card (Finset α) * (4 * Q + 8)))
        (max 1 (max (positiveRetainedDenominatorBound j.val d ta P Va Wa ζa)
          (uniformScaledRetainedDenominatorBound j.val d ti P Vi Wi ζi)))
        (max 1 (max ca ci) * Real.exp (Fintype.card (Finset α) * (4 * Q + 8) + Q))
        (⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ + 4) (R0 + 1 / 4) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((height : ℝ) ^ rows.card *
          (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval height y‖ ≤ 2 * ε := by
  intro d ta ti Va Vi Wa Wi ζa ζi fa fi ca ci Kmax R0 Q hQ hRQ hεa hεi hfa hfi hKQ hKLQ hεQ
  rcases allocatedSlicedGrid_cases B U basis S j i H hgrid hδ hdense
      ((Fintype.card α + 1) * q) T hQT with hsmall | ⟨hsize, hcases⟩
  · obtain ⟨e, he, herr⟩ := exists_allocatedSupportedSliced_bounded_grid_site_expansion
      B U basis hR hσ S q r H step c hH hsubset hcell j i hσ1 hgrid rows hsmall hε hQ hRQ hKQ hKLQ hεQ
    refine ⟨e, he.mono ?_ (le_max_left _ _) ?_ le_rfl le_rfl, ?_⟩
    · exact le_mul_of_one_le_left (Real.exp_nonneg _) (le_max_left _ _)
    · exact le_mul_of_one_le_left (Real.exp_nonneg _) (le_max_left _ _)
    · intro x y hy
      exact (herr x y hy).trans (by linarith)
  · rcases hcases with ⟨ha, hlength⟩ | ⟨hi, hl, hlength⟩
    · let M := torusA * height
      have hM : 0 < M := Nat.mul_pos (blockTorusFactor_pos _ _ _ _) (basisAxisScale_pos (basis j) i)
      let : NeZero M := ⟨hM.ne'⟩
      obtain ⟨e, he, herr⟩ := exists_allocatedSupportedSliced_grid_site_expansion
        B U basis hR hσ S q hq r H step c hH hsubset hcell j i ha hsize hgrid hδ hlength hstep
        A hA P hcP hsP hstride (M := M) rfl rows hrows hBa hε hε1 hσ1 hε hQ hRQ hεa hfa
      refine ⟨e, he.mono ?_ ?_ ?_ le_rfl le_rfl, ?_⟩
      · exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) (Real.exp_nonneg _)
      · exact (le_max_left _ _).trans (le_max_right _ _)
      · exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) (Real.exp_nonneg _)
      · intro x y hy
        simpa only [two_mul] using herr x y hy
    · let M := torusI * height
      have hM : 0 < M := Nat.mul_pos (blockTorusFactor_pos _ _ _ _) (basisAxisScale_pos (basis j) i)
      let : NeZero M := ⟨hM.ne'⟩
      obtain ⟨e, he, herr⟩ := exists_allocatedSupportedSliced_inactive_grid_site_expansion
        B U basis hR hσ S q hq r H step c hH hsubset hcell j i hsize hgrid hi hl hδ hlength hstep
        A hA P hP hsP hstride (M := M) rfl rows hrows hBi hε hε1 hσ1 hε hQ hRQ hεi hfi
      refine ⟨e, he.mono ?_ ?_ ?_ le_rfl le_rfl, ?_⟩
      · exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) (Real.exp_nonneg _)
      · exact (le_max_right _ _).trans (le_max_right _ _)
      · exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) (Real.exp_nonneg _)
      · intro x y hy
        simpa only [two_mul] using herr x y hy

end Erdos3.VectorPolynomial

end

section

namespace Erdos3
open scoped NNReal

def slicedGridSiteLog {A : Type*} [Semiring A]
    (n d ta ti : ℕ) (D p E : A) : A :=
  positiveRetainedComplexityLog n d ta p p p E +
  uniformSpectrumCardLog n d ti p p p E + uniformRetainedFrequencyLog n d ti p p p E +
  uniformRetainedDenominatorLog n d ti p p p E +
  positiveSpectrumCardLog n d ta p p p 0 + uniformSpectrumSizeLog n d ti p p p +
  (D + 2) * p + E + 2 * D + 20

theorem slicedGridSiteLog_bounds (n d ta ti : ℕ) {D p E : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hE : 0 ≤ E) :
    let Q := slicedGridSiteLog n d ta ti D p E
    0 ≤ Q ∧ p ≤ Q ∧ E ≤ Q ∧
      positiveRetainedComplexityLog n d ta p p p E + 2 * D + 13 ≤ Q ∧
      uniformSpectrumCardLog n d ti p p p E ≤ Q ∧
      uniformRetainedFrequencyLog n d ti p p p E + 2 * D + 13 ≤ Q ∧
      uniformRetainedDenominatorLog n d ti p p p E ≤ Q ∧
      positiveSpectrumCardLog n d ta p p p 0 + 2 + E ≤ Q ∧
      uniformSpectrumSizeLog n d ti p p p + 2 + E ≤ Q ∧
      D * p ≤ Q ∧ 2 * D + (D + 2) * p + 1 ≤ Q := by
  have ha := (positiveRetainedComplexityLog_bounds n d ta hp hp hp hE).1
  obtain ⟨_, hc, hf, ht⟩ := uniformRetainedLogs_nonneg n d ti hp hp hp hE
  have hca := (positiveRetainedLogs_nonneg n d ta hp hp hp (le_refl (0 : ℝ))).2.1
  have hci := (uniformSpectrumLogs_nonneg n d ti hp hp hp).2.2
  have hDp := mul_nonneg hD hp
  dsimp only
  unfold slicedGridSiteLog
  constructor; · positivity
  constructor; · nlinarith
  constructor; · nlinarith
  constructor; · nlinarith
  constructor; · nlinarith
  constructor; · nlinarith
  constructor; · nlinarith
  constructor; · nlinarith
  constructor; · nlinarith
  constructor <;> nlinarith

theorem boundedGridResources_exp_bound (c d K : ℕ) {D p : ℝ}
    (_hD : 0 ≤ D) (hp : 0 ≤ p) (hc : (c : ℝ) ≤ D) (hd : (d : ℝ) ≤ D)
    (hK : (K : ℝ) ≤ Real.exp p) :
    (K : ℝ) ^ d ≤ Real.exp (D * p) ∧
    (((d * (2 * (K : ℝ≥0) ^ 2) * (K : ℝ≥0) ^ d) * (2 : ℝ≥0) ^ c : ℝ≥0) : ℝ) ≤
      Real.exp (2 * D + (D + 2) * p + 1) := by
  have hKd := pow_le_exp_mul_of_le_exp (Nat.cast_nonneg K) hK hp d hd
  have hK2 := pow_le_exp_mul_of_le_exp (Nat.cast_nonneg K) hK hp 2 le_rfl
  have ht : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have htc : (2 : ℝ) ^ c ≤ Real.exp D := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) ht (by norm_num) c hc
  have hdr : (d : ℝ) ≤ Real.exp D := hd.trans (by linarith [Real.add_one_le_exp D])
  have hprod := mul_le_mul
    (mul_le_mul (mul_le_mul hdr (mul_le_mul ht hK2 (by positivity) (Real.exp_nonneg _))
      (by positivity) (by positivity)) hKd (by positivity) (by positivity))
    htc (by positivity) (by positivity)
  simp only [← Real.exp_add] at hprod
  refine ⟨hKd, ?_⟩
  simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast, NNReal.coe_ofNat]
  exact hprod.trans_eq (by congr 1; ring)

theorem slicedGridSite_numerics (c n d ta ti K : ℕ) {D p E U Va Vi Wa Wi ε R0 : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hc : (c : ℝ) ≤ D) (hd : (d : ℝ) ≤ D)
    (hU : 1 ≤ U) (hVa : 0 ≤ Va) (hVi : 0 ≤ Vi) (hWa : 0 ≤ Wa) (hWi : 0 ≤ Wi)
    (hUp : U ≤ Real.exp p) (hVap : Va ≤ Real.exp p) (hVip : Vi ≤ Real.exp p)
    (hWap : Wa ≤ Real.exp p) (hWip : Wi ≤ Real.exp p)
    (hKp : (K : ℝ) ≤ Real.exp p) (hRp : R0 + 1 / 4 ≤ Real.exp p)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hεE : ε⁻¹ ≤ Real.exp E) :
    let Q := slicedGridSiteLog n d ta ti D p E
    let ζa := positiveModerateRetainedBias n d ta U Va Wa ε
    let ζi := uniformBlockRetainedBias n d ti U Vi Wi ε
    let ca := positiveModerateSpectrumCardBudget n d ta U Va Wa 1 + 1
    let ci := uniformSpectrumAbsoluteCap n d ti U Vi Wi
    0 ≤ Q ∧ R0 + 1 / 4 ≤ Real.exp Q ∧
      (ε / (ca + 1))⁻¹ ≤ Real.exp Q ∧ (ε / (ci + 1))⁻¹ ≤ Real.exp Q ∧
      (((CircleFourier.characterLipConstant * (d * Real.toNNReal (positiveRetainedFrequencyBound n d U Va ζa)) + 4) *
        (2 : ℝ≥0) ^ c : ℝ≥0) : ℝ) ≤ Real.exp Q ∧
      (((CircleFourier.characterLipConstant * (d * Real.toNNReal (uniformScaledRetainedFrequencyBound n d U Vi ζi)) + 4) *
        (2 : ℝ≥0) ^ c : ℝ≥0) : ℝ) ≤ Real.exp Q ∧
      (K : ℝ) ^ d ≤ Real.exp Q ∧
      (((d * (2 * (K : ℝ≥0) ^ 2) * (K : ℝ≥0) ^ d) * (2 : ℝ≥0) ^ c : ℝ≥0) : ℝ) ≤ Real.exp Q ∧
      ε⁻¹ ≤ Real.exp Q ∧
      max 1 (max (positiveModerateSpectrumCardBudget n d ta U Va Wa ε)
        (uniformSpectrumSizeConstant n d ti U Vi Wi /
          ε ^ max (majorArcSpectrumExponent n d) (majorArcLengthExponent n * ti))) ≤ Real.exp Q ∧
      max 1 (max (positiveRetainedDenominatorBound n d ta U Va Wa ζa)
        (uniformScaledRetainedDenominatorBound n d ti U Vi Wi ζi)) ≤ Real.exp Q ∧
      max 1 (max ca ci) ≤ Real.exp Q := by
  intro Q ζa ζi ca ci
  obtain ⟨hQ, hpQ, hEQ, haQ, hsQ, hfQ, htQ, hcaQ, hciQ, hKQ, hKLQ⟩ :=
    slicedGridSiteLog_bounds n d ta ti hD hp hE
  obtain ⟨ha, haf, hat⟩ := positiveRetainedComplexity_exp_bounds n d ta hU hVa hWa hε
    hp hp hp hE hUp hVap hWap hεE
  have hi := uniformSpectrumCardBound_exp_bound n d ti hU hVi hWi hε hp hp hp hE hUp hVip hWip hεE
  obtain ⟨hif, hit⟩ := uniformScaledRetained_exp_bounds n d ti hU hVi hWi hε hε1
    hp hp hp hE hUp hVip hWip hεE
  have ha0 := positiveModerateSpectrumCardBudget_exp_bound n d ta hU hVa hWa zero_lt_one
    hp hp hp (le_refl (0 : ℝ)) hUp hVap hWap (by norm_num)
  have hi0 := uniformSpectrumAbsoluteCap_exp_bound n d ti hU hVi hWi hp hp hp hUp hVip hWip
  have halog := (positiveRetainedLogs_nonneg n d ta hp hp hp (le_refl (0 : ℝ))).2.1
  have hilog := (uniformSpectrumLogs_nonneg n d ti hp hp hp).2.2
  have hca : ca + 1 ≤ Real.exp (positiveSpectrumCardLog n d ta p p p 0 + 2) := by
    have h1 := one_add_le_exp_succ halog ha0
    have h2 := one_add_le_exp_succ (by linarith : 0 ≤ positiveSpectrumCardLog n d ta p p p 0 + 1) h1
    dsimp [ca]
    convert h2 using 1 <;> ring_nf
  have hci : ci + 1 ≤ Real.exp (uniformSpectrumSizeLog n d ti p p p + 2) := by
    have h1 := one_add_le_exp_succ (by linarith : 0 ≤ uniformSpectrumSizeLog n d ti p p p + 1) hi0
    dsimp [ci]
    convert h1 using 1 <;> ring_nf
  have hfrac {C b : ℝ} (hb : C + 1 ≤ Real.exp b) (hbQ : b + E ≤ Q) :
      (ε / (C + 1))⁻¹ ≤ Real.exp Q := by
    rw [inv_div, div_eq_mul_inv]
    exact ((mul_le_mul hb hεE (inv_nonneg.mpr hε.le) (Real.exp_nonneg _)).trans_eq
      (Real.exp_add _ _).symm).trans (Real.exp_le_exp.mpr hbQ)
  have halogE := (positiveRetainedComplexityLog_bounds n d ta hp hp hp hE).1
  have hiflog := (uniformRetainedLogs_nonneg n d ti hp hp hp hE).2.2.1
  have hLa := siteCharacterLipschitz_exp_bound c d hD halogE hc hd haf
  have hLi := siteCharacterLipschitz_exp_bound c d hD hiflog hc hd hif
  obtain ⟨hK, hKL⟩ := boundedGridResources_exp_bound c d K hD hp hc hd hKp
  have haQ' : positiveRetainedComplexityLog n d ta p p p E ≤ Q := by linarith
  have hcaQ' : positiveSpectrumCardLog n d ta p p p 0 + 2 ≤ Q := by linarith
  have hciQ' : uniformSpectrumSizeLog n d ti p p p + 2 ≤ Q := by linarith
  have h1 : (1 : ℝ) ≤ Real.exp Q := Real.one_le_exp_iff.mpr hQ
  refine ⟨hQ, hRp.trans (Real.exp_le_exp.mpr hpQ), hfrac hca hcaQ, hfrac hci hciQ,
    hLa.trans (Real.exp_le_exp.mpr haQ), hLi.trans (Real.exp_le_exp.mpr hfQ),
    hK.trans (Real.exp_le_exp.mpr hKQ), hKL.trans (Real.exp_le_exp.mpr hKLQ),
    hεE.trans (Real.exp_le_exp.mpr hEQ), ?_, ?_, ?_⟩
  · exact max_le h1 (max_le (ha.trans (Real.exp_le_exp.mpr haQ')) (hi.trans (Real.exp_le_exp.mpr hsQ)))
  · exact max_le h1 (max_le (hat.trans (Real.exp_le_exp.mpr haQ')) (hit.trans (Real.exp_le_exp.mpr htQ)))
  · exact max_le h1 (max_le ((le_add_of_nonneg_right zero_le_one).trans
      (hca.trans (Real.exp_le_exp.mpr hcaQ'))) ((le_add_of_nonneg_right zero_le_one).trans
      (hci.trans (Real.exp_le_exp.mpr hciQ'))))

theorem slicedGridPointCap_exp_bound (c n d ta ti K : ℕ) {D p U Va Vi Wa Wi : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hc : (c : ℝ) ≤ D) (hd : (d : ℝ) ≤ D)
    (hU : 1 ≤ U) (hVa : 0 ≤ Va) (hVi : 0 ≤ Vi) (hWa : 0 ≤ Wa) (hWi : 0 ≤ Wi)
    (hUp : U ≤ Real.exp p) (hVap : Va ≤ Real.exp p) (hVip : Vi ≤ Real.exp p)
    (hWap : Wa ≤ Real.exp p) (hWip : Wi ≤ Real.exp p) (hKp : (K : ℝ) ≤ Real.exp p) :
    max 1 (max ((K : ℝ) ^ d) (max (positiveModerateSpectrumCardBudget n d ta U Va Wa 1 + 1)
      (uniformSpectrumAbsoluteCap n d ti U Vi Wi))) ≤ Real.exp (slicedGridSiteLog n d ta ti D p 0) := by
  have hRp : (0 : ℝ) + 1 / 4 ≤ Real.exp p := by
    have := Real.one_le_exp_iff.mpr hp
    linarith
  obtain ⟨hQ, _, _, _, _, _, hK, _, _, _, _, hcap⟩ :=
    slicedGridSite_numerics c n d ta ti K hD hp (le_refl (0 : ℝ)) hc hd hU hVa hVi hWa hWi
      hUp hVap hVip hWap hWip hKp hRp zero_lt_one le_rfl (by norm_num : (1 : ℝ)⁻¹ ≤ Real.exp 0)
  exact max_le (Real.one_le_exp_iff.mpr hQ) (max_le hK ((le_max_right _ _).trans hcap))

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (R : Fin m → ℝ) (j : Fin m) (i : Fin (n j))
variable (α : Type*) [Fintype α] (d T : ℕ)
local notation "degree" => Fin.val j + 1

theorem allocatedSlicedGridPointCap_geometry_exp_bound {δ D v w t P p₀ : ℝ}
    (hD : 0 ≤ D) (hv : 0 ≤ v) (hw : 0 ≤ w) (ht : 0 ≤ t) (hp₀ : 0 ≤ p₀)
    (hδ : 0 < δ) (hR : 0 < R j)
    (hq : (Fintype.card α : ℝ) ≤ D) (hdegree : ((degree : ℕ) : ℝ) ≤ D) (hd : (d : ℝ) ≤ D)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ D)
    (hb : (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ D)
    (hRv : R j ≤ Real.exp v) (hRi : (R j)⁻¹ ≤ Real.exp v)
    (hδw : δ⁻¹ ≤ Real.exp w) (hT : (T : ℝ) ≤ Real.exp t)
    (hcoeff : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree) : ℝ) ≤ Real.exp v)
    (hP : 1 ≤ P) (hPp₀ : P ≤ Real.exp p₀) :
    allocatedSlicedGridPointCap (G := G) (α := α) B (R := R) j i δ P T d ≤
      Real.exp (slicedGridSiteLog j.val d ((layerTailDegree m + 1) * d) (degree * d)
        D (slicedGridGeometryLog D v w t + p₀) 0) := by
  let p := slicedGridGeometryLog D v w t + p₀
  have hg : 0 ≤ slicedGridGeometryLog D v w t := by unfold slicedGridGeometryLog; positivity
  have hp : 0 ≤ p := add_nonneg hg hp₀
  have hgp : Real.exp (slicedGridGeometryLog D v w t) ≤ Real.exp p :=
    Real.exp_le_exp.mpr (le_add_of_nonneg_right hp₀)
  have hPp : P ≤ Real.exp p := hPp₀.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_left hg))
  obtain ⟨hVa, hVi, hWa, hWi, hK, _⟩ := allocatedSlicedGrid_geometry_bounds
    B R j i (Fintype.card α) d T hD hv hw ht hδ hR hq hdegree hd htail hb hRv hRi hδw hT hcoeff
  have hγ := principalProfileSize_pos hR (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
  exact slicedGridPointCap_exp_bound (Fintype.card α) j.val d ((layerTailDegree m + 1) * d) (degree * d)
    (allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i T) hD hp hq hd hP
    (by positivity) (by positivity) (by positivity) (by positivity) hPp
    (hVa.trans hgp) (hVi.trans hgp) (hWa.trans hgp) (hWi.trans hgp) (hK.trans hgp)

theorem allocatedSlicedGridNaturalPointCap_geometry_exp_bound {δ D v w t P p₀ : ℝ}
    (hD : 0 ≤ D) (hv : 0 ≤ v) (hw : 0 ≤ w) (ht : 0 ≤ t) (hp₀ : 0 ≤ p₀)
    (hδ : 0 < δ) (hR : 0 < R j)
    (hq : (Fintype.card α : ℝ) ≤ D) (hdegree : ((degree : ℕ) : ℝ) ≤ D) (hd : (d : ℝ) ≤ D)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ D)
    (hb : (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ D)
    (hRv : R j ≤ Real.exp v) (hRi : (R j)⁻¹ ≤ Real.exp v)
    (hδw : δ⁻¹ ≤ Real.exp w) (hT : (T : ℝ) ≤ Real.exp t)
    (hcoeff : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree) : ℝ) ≤ Real.exp v)
    (hP : 1 ≤ P) (hPp₀ : P ≤ Real.exp p₀) :
    (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)) + 1) ^ d *
    allocatedSlicedGridPointCap (G := G) (α := α) B (R := R) j i δ P T d ≤
      Real.exp (slicedGridSiteLog j.val d ((layerTailDegree m + 1) * d) (degree * d)
        D (slicedGridGeometryLog D v w t + p₀) 0 + D * (v + 1)) := by
  have hcap := allocatedSlicedGridPointCap_geometry_exp_bound B R j i α d T
    hD hv hw ht hp₀ hδ hR hq hdegree hd htail hb hRv hRi hδw hT hcoeff hP hPp₀
  have hγ := principalProfileSize_pos hR (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
  have hslots : ((layerIntegerPrincipalSlots (G := G) B j i).card : ℝ) ≤ D := by
    simpa only [layerIntegerPrincipalSlots_card] using hb
  have hγv := (principalProfileSize_exp_bounds _ hR hslots hRv hRi).1
  have hadd : principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)) + 1 ≤ Real.exp (v + 1) := by
    simpa only [add_comm 1 (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))] using one_add_le_exp_succ hv hγv
  have hpow := pow_le_exp_mul_of_le_exp (by positivity) hadd (by positivity) d hd
  have hmul := mul_le_mul hpow hcap
    (le_trans zero_le_one (le_max_left _ _)) (Real.exp_nonneg _)
  exact hmul.trans_eq (by rw [← Real.exp_add]; congr 1; ring)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uα

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "denom" => inactiveDenominator gamma
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "torusA" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)
local notation "torusI" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

include hq in
theorem exists_allocatedSupportedSliced_budgeted_grid_site_expansion
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j,Sum.inr i⟩)
    {δ : ℝ} (hδ : 0 < δ)
    (hdense : ∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ ≤
      (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (T : ℕ) (hQT : (((Fintype.card α + 1) * q : ℕ) : ℝ) / δ ≤ T)
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hBa : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hσ1 : σ j ≤ 1) :
    let d := rows.card
    let ta := (layerTailDegree m + 1) * d
    let ti := degree * d
    let Va := ((torusA : ℝ) / (2 * gamma)) / δ ^ degree
    let Vi := (torusI : ℝ) * cost / δ ^ degree
    let Wa := (torusA : ℝ) ^ d / δ ^ ta
    let Wi := ((torusI : ℝ) * cost) ^ d / δ ^ ti
    let ζa := positiveModerateRetainedBias j.val d ta P Va Wa ε
    let ζi := uniformBlockRetainedBias j.val d ti P Vi Wi ε
    let _fa := Real.toNNReal (positiveRetainedFrequencyBound j.val d P Va ζa)
    let _fi := Real.toNNReal (uniformScaledRetainedFrequencyBound j.val d P Vi ζi)
    let _ca := positiveModerateSpectrumCardBudget j.val d ta P Va Wa 1 + 1
    let _ci := uniformSpectrumAbsoluteCap j.val d ti P Vi Wi
    let Kmax := allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i T
    let R0 := (d : ℝ) *
      ((Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) * R j)
    ∀ {D p E : ℝ}, 0 ≤ D → 0 ≤ p → 0 ≤ E →
      (Fintype.card α : ℝ) ≤ D → (d : ℝ) ≤ D →
      P ≤ Real.exp p → Va ≤ Real.exp p → Vi ≤ Real.exp p →
      Wa ≤ Real.exp p → Wi ≤ Real.exp p →
      (Kmax : ℝ) ≤ Real.exp p → R0 + 1 / 4 ≤ Real.exp p → ε⁻¹ ≤ Real.exp E →
    let Q := slicedGridSiteLog j.val d ta ti D p E
    let O := siteExponentialOutputLog (Fintype.card (Finset α)) Q
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (R0 + 1 / 4) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((height : ℝ) ^ rows.card *
          (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval height y‖ ≤ 2 * ε := by
  intro d ta ti Va Vi Wa Wi ζa ζi fa fi ca ci Kmax R0 D p E hD hp hE hc hd hPp hVap hVip hWap hWip hKp hRp hεE Q O
  have hgamma : 0 < gamma := principalProfileSize_pos (hR j) _
  have hVa : 0 ≤ Va := by dsimp [Va]; positivity
  have hVi : 0 ≤ Vi := by dsimp [Vi]; positivity
  have hWa : 0 ≤ Wa := by dsimp [Wa]; positivity
  have hWi : 0 ≤ Wi := by dsimp [Wi]; positivity
  obtain ⟨hQ, hRQ, hεa, hεi, hfa, hfi, hKQ, hKLQ, hεQ, hsizeQ, hperiodQ, hcapQ⟩ :=
    slicedGridSite_numerics (Fintype.card α) j.val d ta ti Kmax hD hp hE hc hd hP hVa hVi hWa hWi
      hPp hVap hVip hWap hWip hKp hRp hε hε1 hεE
  obtain ⟨e, he, herr⟩ := exists_allocatedSupportedSliced_mixed_grid_site_expansion
    B U basis hR hσ S q hq r H step c hH hsubset hcell j i hgrid hδ hdense T hQT hstep A hA P hP hcP hsP hstride
    rows hrows hBa hBi hε hε1 hσ1 hQ hRQ hεa hεi hfa hfi hKQ hKLQ hεQ
  obtain ⟨hT, hperiod, hcap, hLip, _⟩ := siteExponentialOutput_bounds
    (Fintype.card (Finset α)) (Fintype.card (Finset α)) le_rfl hQ hsizeQ hperiodQ hcapQ
  refine ⟨e, he.mono hT hperiod hcap ?_ le_rfl, herr⟩
  exact_mod_cast hLip

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uα

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "denom" => inactiveDenominator gamma
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "torusA" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)
local notation "torusI" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

include hq in
theorem exists_allocatedSupportedSliced_geometry_grid_site_expansion
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j,Sum.inr i⟩)
    {δ : ℝ} (hδ : 0 < δ)
    (hdense : ∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ ≤
      (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (T : ℕ) (hQT : (((Fintype.card α + 1) * q : ℕ) : ℝ) / δ ≤ T)
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hBa : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {D v w t p₀ E ε : ℝ}
    (hD : 0 ≤ D) (hv : 0 ≤ v) (hw : 0 ≤ w) (ht : 0 ≤ t) (hp₀ : 0 ≤ p₀) (hE : 0 ≤ E)
    (hcube : (Fintype.card α : ℝ) ≤ D) (hdegree : ((degree : ℕ) : ℝ) ≤ D)
    (hrowsD : (rows.card : ℝ) ≤ D) (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ D)
    (hblocks : (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ D)
    (hRv : R j ≤ Real.exp v) (hRi : (R j)⁻¹ ≤ Real.exp v)
    (hδw : δ⁻¹ ≤ Real.exp w) (hT : (T : ℝ) ≤ Real.exp t)
    (hcoeff : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree) : ℝ) ≤ Real.exp v)
    (hPp₀ : P ≤ Real.exp p₀)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hεE : ε⁻¹ ≤ Real.exp E) (hσ1 : σ j ≤ 1) :
    let p := slicedGridGeometryLog D v w t + p₀
    let Q := slicedGridSiteLog j.val rows.card ((layerTailDegree m + 1) * rows.card)
      (degree * rows.card) D p E
    let O := siteExponentialOutputLog (Fintype.card (Finset α)) Q
    let R0 := (rows.card : ℝ) *
      ((Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) * R j)
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (R0 + 1 / 4) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((height : ℝ) ^ rows.card *
          (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval height y‖ ≤ 2 * ε := by
  intro p Q O R0
  have hg : 0 ≤ slicedGridGeometryLog D v w t := by
    unfold slicedGridGeometryLog
    positivity
  have hp : 0 ≤ p := add_nonneg hg hp₀
  have hgp : Real.exp (slicedGridGeometryLog D v w t) ≤ Real.exp p :=
    Real.exp_le_exp.mpr (le_add_of_nonneg_right hp₀)
  have hPp : P ≤ Real.exp p := hPp₀.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_left hg))
  obtain ⟨hVa, hVi, hWa, hWi, hK, hR0⟩ := allocatedSlicedGrid_geometry_bounds
    B R j i (Fintype.card α) rows.card T hD hv hw ht hδ (hR j)
    hcube hdegree hrowsD htail hblocks hRv hRi hδw hT hcoeff
  exact exists_allocatedSupportedSliced_budgeted_grid_site_expansion
    B U basis hR hσ S q hq r H step c hH hsubset hcell j i hgrid hδ hdense T hQT hstep
    A hA P hP hcP hsP hstride rows hrows hBa hBi hε hε1 hσ1
    hD hp hE hcube hrowsD hPp (hVa.trans hgp) (hVi.trans hgp)
    (hWa.trans hgp) (hWi.trans hgp) (hK.trans hgp) (hR0.trans hgp) hεE

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uα

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "denom" => inactiveDenominator gamma
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "torusA" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)
local notation "torusI" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

include hq in
theorem exists_allocatedSupportedSliced_natural_grid_site_expansion
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j,Sum.inr i⟩)
    {δ : ℝ} (hδ : 0 < δ)
    (hdense : ∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ ≤
      (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (T : ℕ) (hQT : (((Fintype.card α + 1) * q : ℕ) : ℝ) / δ ≤ T)
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hBa : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {D v w t p₀ E ε : ℝ}
    (hD : 0 ≤ D) (hv : 0 ≤ v) (hw : 0 ≤ w) (ht : 0 ≤ t) (hp₀ : 0 ≤ p₀) (hE : 0 ≤ E)
    (hcube : (Fintype.card α : ℝ) ≤ D) (hdegree : ((degree : ℕ) : ℝ) ≤ D)
    (hrowsD : (rows.card : ℝ) ≤ D) (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ D)
    (hblocks : (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ D)
    (hRv : R j ≤ Real.exp v) (hRi : (R j)⁻¹ ≤ Real.exp v)
    (hδw : δ⁻¹ ≤ Real.exp w) (hT : (T : ℝ) ≤ Real.exp t)
    (hcoeff : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree) : ℝ) ≤ Real.exp v)
    (hPp₀ : P ≤ Real.exp p₀)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hεE : ε⁻¹ ≤ Real.exp E) (hσ1 : σ j ≤ 1) :
    let p := slicedGridGeometryLog D v w t + p₀
    let E' := E + D * (v + 1) + 1
    let Q := slicedGridSiteLog j.val rows.card ((layerTailDegree m + 1) * rows.card)
      (degree * rows.card) D p E'
    let O := siteExponentialOutputLog (Fintype.card (Finset α)) Q + (D + 1) * (v + 1)
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (slicedGridGeometryLog D v w t + (D + v + 8))) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((allocatedPrincipalGridScale (G := G) B U basis (R := R) j i : ℝ) ^ rows.card *
          (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) -
          e.integerEval (allocatedPrincipalGridScale (G := G) B U basis (R := R) j i) y‖ ≤ ε := by
  intro p E' Q O
  have hγ : 0 < gamma := principalProfileSize_pos (hR j) _
  have hslots : ((layerIntegerPrincipalSlots (G := G) B j i).card : ℝ) ≤ D := by
    simpa only [layerIntegerPrincipalSlots_card] using hblocks
  obtain ⟨hγv, hγg⟩ := principalProfileSize_exp_bounds _ (hR j) hslots hRv hRi
  let ζ := ε / (2 * (gamma + 1) ^ rows.card)
  obtain ⟨hζ, hζ1, hζE, herrScale⟩ := ScalarSiteExpansion.ceilScaleAccuracy_bounds rows.card
    hγ hε hε1 hD hv hrowsD hγv hεE
  have hE' : 0 ≤ E' := by dsimp [E']; positivity
  obtain ⟨e, he, herr⟩ := exists_allocatedSupportedSliced_geometry_grid_site_expansion
    B U basis hR hσ S q hq r H step c hH hsubset hcell j i hgrid hδ hdense T hQT hstep
    A hA P hP hcP hsP hstride rows hrows hBa hBi hD hv hw ht hp₀ hE'
    hcube hdegree hrowsD htail hblocks hRv hRi hδw hT hcoeff hPp₀ hζ hζ1 hζE hσ1
  have hgeometry := allocatedSlicedGrid_geometry_bounds B R j i (Fintype.card α) rows.card T
    hD hv hw ht hδ (hR j) hcube hdegree hrowsD htail hblocks hRv hRi hδw hT hcoeff
  have hR0 := hgeometry.2.2.2.2.2
  have hR0pos : 0 ≤ (rows.card : ℝ) *
      ((Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) * R j) + 1 / 4 := by
    have hRj := hR j
    positivity
  refine ⟨e.atCeilScale height rows.card gamma, ?_, ?_⟩
  · exact ScalarSiteExpansion.atCeilScale_exp_bounds e height rows.card (basisAxisScale_pos (basis j) i)
      hγ hD hv hR0pos hrowsD hγv hγg hR0 he
  · intro x y hy
    have hb := ScalarSiteExpansion.atCeilScale_integer_error e height rows.card
      (basisAxisScale_pos (basis j) i) hγ y
      (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x
        (fun t => booleanCoefficient y t)).toReal (by positivity : 0 ≤ 2 * ζ) (herr x y hy)
    exact hb.trans_eq herrScale

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell grid
local notation "height" => (fun a : gridAxes => basisAxisScale (b (Sigma.fst (ig a))) (Sigma.snd (ig a)))

theorem exists_allocatedSupportedSliced_full_grid_site_expansion
    (hq : 0 < q) {δ : ℝ} (hδ : 0 < δ)
    (hdense : ∀ t, δ * allocatedPrincipalSides B U b S t ≤ (H t : ℝ))
    (T : ℕ) (hQT : (((Fintype.card α + 1) * q : ℕ) : ℝ) / δ ≤ T)
    (hstep : ∀ t, 0 < step t)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ t, ((step t * q : ℕ) : ℝ) ≤ P)
    (hrows : ∀ j t, t ∈ rowSets j → t.card ≤ j.val + 1)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val (rowSets j).card
      ((layerTailDegree m + 1) * (rowSets j).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val (rowSets j).card
      ((j.val + 1) * (rowSets j).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {D v w t p₀ E ε : ℝ}
    (hD : 0 ≤ D) (hv : 0 ≤ v) (hw : 0 ≤ w) (ht : 0 ≤ t) (hp₀ : 0 ≤ p₀) (hE : 0 ≤ E)
    (hcube : (Fintype.card α : ℝ) ≤ D) (hdegree : ∀ j : Fin m, ((j.val + 1 : ℕ) : ℝ) ≤ D)
    (hrowsD : ∀ j, ((rowSets j).card : ℝ) ≤ D)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ D)
    (hblocks : ∀ j i, (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ D)
    (hRv : ∀ j, R j ≤ Real.exp v) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp v)
    (hδw : δ⁻¹ ≤ Real.exp w) (hT : (T : ℝ) ≤ Real.exp t)
    (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp v)
    (hPp₀ : P ≤ Real.exp p₀) (haxes : (Fintype.card gridAxes : ℝ) ≤ D)
    (hε : 0 < ε) (hεE : ε⁻¹ ≤ Real.exp E) (hσ1 : ∀ j, σ j ≤ 1) :
    let p := slicedGridGeometryLog D v w t + p₀
    let L := fun j : Fin m => fun e : ℝ => slicedGridSiteLog j.val (rowSets j).card
      ((layerTailDegree m + 1) * (rowSets j).card) ((j.val + 1) * (rowSets j).card) D p e
    let Cp := ∑ j, (L j 0 + D * (v + 1))
    let E' := uniformProductAccuracyLog D Cp E + D * (v + 1) + 1
    let Op := ∑ j, (siteExponentialOutputLog (Fintype.card (Finset α)) (L j E') + (D + 1) * (v + 1))
    ∃ e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α),
      (∀ a, (e a).Bounds (Real.exp Op) (Real.exp Op) (Real.exp Op)
        ⟨Real.exp Op, Real.exp_nonneg _⟩ (Real.exp (slicedGridGeometryLog D v w t + (D + v + 8)))) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (z : AllocatedFrozenJetRows B U b S rowTypes),
        ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ) *
          (allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x z : ℂ) -
          allocatedFullGridSiteApproximation B U b S rowSets e z‖ ≤ ε := by
  intro p L Cp E' Op
  have hp : 0 ≤ p := by dsimp [p, slicedGridGeometryLog]; positivity
  have hL (j : Fin m) {e : ℝ} (he : 0 ≤ e) : 0 ≤ L j e :=
    (slicedGridSiteLog_bounds j.val (rowSets j).card _ _ hD hp he).1
  have hCp : 0 ≤ Cp := Finset.sum_nonneg (fun j _ => add_nonneg (hL j le_rfl) (by positivity))
  let C := Real.exp Cp
  let η := uniformProductAccuracy (Fintype.card gridAxes) C ε
  obtain ⟨hη, hη1, _⟩ := uniformProductAccuracy_spec (Fintype.card gridAxes) (Real.exp_nonneg Cp) hε
  have hηE := uniformProductAccuracy_inverse_exp_bound (Fintype.card gridAxes)
    (Real.exp_nonneg Cp) hε hD hCp hE haxes le_rfl hεE
  have hEt : 0 ≤ uniformProductAccuracyLog D Cp E := uniformProductAccuracyLog_nonneg hD hCp hE
  have hE' : 0 ≤ E' := by dsimp [E']; positivity
  have hbound (j : Fin m) : L j 0 + D * (v + 1) ≤ Cp :=
    Finset.single_le_sum (fun k _ => add_nonneg (hL k le_rfl) (by positivity)) (Finset.mem_univ j)
  have hcap (a : gridAxes) (x : G → IntegerScalarCubeBox α S.value) (z : rowSets (ig a).1 → ℤ) :
      ‖(((axisN a : ℝ) ^ (rowSets (ig a).1).card *
        (allocatedSupportedSlicedPhysicalGridPMF B U b hR hσ S q r H step c hH hsubset hcell
          (ig a).1 (ig a).2 (rowSets (ig a).1) x z).toReal : ℝ) : ℂ)‖ ≤ C := by
    have hc := allocatedSupportedSlicedPhysicalGridPMF_natural_norm_le B U b hR hσ S q hq r H step c hH hsubset hcell
      (ig a).1 (ig a).2 (allocatedGridIntegerAxis_grid B U b S a) hδ
      (fun b v => hdense _) T hQT (fun b v => hstep _) A hA P hP hcP hsP (fun b v => hstride _)
      (rowSets (ig a).1) (hrows (ig a).1) (hBa _ _) (hBi _ _) x z
    have hb := allocatedSlicedGridNaturalPointCap_geometry_exp_bound B R (ig a).1 (ig a).2 α
      (rowSets (ig a).1).card T hD hv hw ht hp₀ hδ (hR _) hcube (hdegree _) (hrowsD _)
      htail (hblocks _ _) (hRv _) (hRi _) hδw hT (hcoeff _) hP hPp₀
    exact hc.trans (hb.trans (Real.exp_le_exp.mpr (hbound _)))
  have hex (a : gridAxes) := exists_allocatedSupportedSliced_natural_grid_site_expansion
    B U b hR hσ S q hq r H step c hH hsubset hcell (ig a).1 (ig a).2
    (allocatedGridIntegerAxis_grid B U b S a) hδ (fun b v => hdense _) T hQT (fun b v => hstep _)
    A hA P hP hcP hsP (fun b v => hstride _) (rowSets (ig a).1) (hrows (ig a).1) (hBa _ _) (hBi _ _)
    hD hv hw ht hp₀ hEt hcube (hdegree _) (hrowsD _) htail (hblocks _ _) (hRv _) (hRi _)
    hδw hT (hcoeff _) hPp₀ hη hη1 hηE (hσ1 _)
  choose e he herr using hex
  refine ⟨e, ?_, ?_⟩
  · intro a
    have hO : siteExponentialOutputLog (Fintype.card (Finset α)) (L (ig a).1 E') + (D + 1) * (v + 1) ≤ Op :=
      Finset.single_le_sum (fun k _ => add_nonneg
        (siteExponentialOutputLog_nonneg _ (hL k hE')) (by positivity)) (Finset.mem_univ (ig a).1)
    have hb := Real.exp_le_exp.mpr hO
    exact (he a).mono hb hb hb (NNReal.coe_le_coe.mp hb) le_rfl
  · exact allocatedSupportedSlicedFullGridNaturalSite_error B U b hR hσ S rowSets H step c hH hsubset q r hcell
      e (Real.exp_nonneg Cp) hε hcap herr

end Erdos3.VectorPolynomial

end

end OAI
