/- Modified for ProveIt: allow 400,000 elaboration heartbeats locally for
exists_allocatedActualProfileFourier_bound on Lean 4.32. All upstream theorem
statements and proof steps are unchanged. -/
import OAI.Combinatorics.Progressions.Dynamics.AllocatedIdealCoverRadiusBudget
import OAI.Combinatorics.Progressions.Dynamics.AllocatedNormalizedScaleBudget
import OAI.Combinatorics.Progressions.Estimates.AllocatedSeparatedGeometry
import OAI.Combinatorics.Progressions.Fourier.AllocatedSiteErrorFourierBudget
import OAI.Combinatorics.Progressions.Geometry.AllocatedInactiveSupportBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

def allocatedIdealCoverInputLog {A : Type*} [Semiring A] (m : ℕ) (D c : A) : A :=
  allocatedSiteCoefficientLog D + (m + 1 : ℕ) * D + c + 4

theorem allocatedIdealCoverInputLog_bounds (m : ℕ) {D c : ℝ}
    (hD : 0 ≤ D) (hc : 0 ≤ c) :
    let L := allocatedIdealCoverInputLog m D c
    0 ≤ L ∧ D ^ 2 + 2 * D ≤ L ∧ (m + 1 : ℕ) * D + 2 ≤ L ∧
      allocatedSiteCoefficientLog D + 1 ≤ L ∧ D ≤ L ∧ c ≤ L := by
  have hm : 0 ≤ (m + 1 : ℕ) * D := mul_nonneg (Nat.cast_nonneg _) hD
  dsimp only [allocatedIdealCoverInputLog, allocatedSiteCoefficientLog]
  constructor
  · positivity
  constructor
  · linarith
  constructor
  · nlinarith [sq_nonneg D]
  constructor
  · linarith
  constructor <;> nlinarith [sq_nonneg D]

noncomputable def allocatedIdealCoverPrimitiveLog {A : Type*} [Semiring A]
    (m : ℕ) (p c : A) : A :=
  8 * allocatedIdealCoverInputLog m (allocatedComparisonDimension m p) c + 14

noncomputable def allocatedIdealCoverPrimitiveRadius (m : ℕ) (p c : ℝ) : ℝ :=
  Real.exp (-allocatedIdealCoverPrimitiveLog m p c)

theorem allocatedIdealCoverPrimitiveRadius_bounds (m : ℕ) {p c : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) :
    0 ≤ allocatedIdealCoverPrimitiveLog m p c ∧
      0 < allocatedIdealCoverPrimitiveRadius m p c ∧
      allocatedIdealCoverPrimitiveRadius m p c ≤ 1 ∧
      (allocatedIdealCoverPrimitiveRadius m p c)⁻¹ = Real.exp (allocatedIdealCoverPrimitiveLog m p c) := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  have hL := (allocatedIdealCoverInputLog_bounds m hD hc).1
  have hlog : 0 ≤ allocatedIdealCoverPrimitiveLog m p c := by
    unfold allocatedIdealCoverPrimitiveLog
    positivity
  refine ⟨hlog, Real.exp_pos _, ?_, ?_⟩
  · exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hlog)
  · simp only [allocatedIdealCoverPrimitiveRadius, Real.exp_neg, inv_inv]

theorem exists_allocatedIdealCoverPrimitiveLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ p : ℝ, 0 ≤ p → allocatedIdealCoverPrimitiveLog m p p ≤ (p + a) ^ a := by
  let poly : Polynomial ℕ := allocatedIdealCoverPrimitiveLog m Polynomial.X Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p hp
  simpa [poly, allocatedIdealCoverPrimitiveLog, allocatedIdealCoverInputLog,
    allocatedSiteCoefficientLog, allocatedComparisonDimension, Polynomial.eval₂_pow] using hbound p hp

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

theorem allocatedIdealCoverRadius_inverse_from_dimensions {D c : ℝ}
    (h : AllocatedComparisonDimensions (G := G) B α (fun j => (rowSets j : Type _)) D)
    (hc : 0 ≤ c) (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ D)
    (hn : ∀ j, (n j : ℝ) ≤ D)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCc : ∀ j, C j ≤ Real.exp c) (j : Fin m) :
    (allocatedIdealCoverRadius (G := G) B rowSets C j)⁻¹ ≤
      Real.exp (8 * allocatedIdealCoverInputLog m D c + 14) := by
  obtain ⟨hL, hLA, hLI, hLW, hLD, hLc⟩ := allocatedIdealCoverInputLog_bounds m h.nonneg hc
  have hde : D ≤ Real.exp D := by linarith [Real.add_one_le_exp D]
  have heL := Real.exp_le_exp.mpr hLD
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpowtwo : (2 : ℝ) ^ Fintype.card α ≤ Real.exp D := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo
      (by norm_num) (Fintype.card α) h.cube
  have hbase : (Fintype.card α : ℝ) + 1 ≤ Real.exp D := by
    linarith [Real.add_one_le_exp D, h.cube]
  have hpow := pow_le_exp_mul_of_le_exp (by positivity) hbase h.nonneg
    (j.val + 1) (h.layer_degree B j)
  have hA : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤
        Real.exp (D ^ 2 + 2 * D) := by
    calc
      _ ≤ Real.exp D * (Real.exp D * Real.exp (D * D)) := by
        gcongr
        exact (h.coefficients j).trans hde
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hIdeal : partitionedIdealRadius α m + 1 ≤ Real.exp (allocatedIdealCoverInputLog m D c) := by
    apply (partitionedIdealRadius_add_one_le_exp α m).trans
    apply Real.exp_le_exp.mpr
    have ht := mul_le_mul_of_nonneg_left h.cube (by positivity : 0 ≤ (m : ℝ) + 1)
    push_cast at hLI
    linarith
  have hWindow (i : Fin (n j)) : allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩ + 1 ≤
      Real.exp (allocatedIdealCoverInputLog m D c) := by
    have h1 := one_add_le_exp_succ (allocatedSiteCoefficientLog_nonneg h.nonneg)
      (allocatedSiteCoefficientRadius_exp_bound B rowSets h ⟨j, i⟩)
    have h2 : allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩ + 1 ≤
        Real.exp (allocatedSiteCoefficientLog D + 1) := by
      simpa only [add_comm] using h1
    exact h2.trans (Real.exp_le_exp.mpr hLW)
  have hrows : ((rowSets j).card : ℝ) ≤ D := by
    simpa only [Fintype.card_coe] using h.rows j
  exact allocatedIdealCoverRadius_inv_le_exp B rowSets hL C hC j
    (hA.trans (Real.exp_le_exp.mpr hLA)) hIdeal ((hn j).trans (hde.trans heL)) hWindow
    (hrows.trans (hde.trans heL)) ((hI j).trans (hde.trans heL))
    ((hCc j).trans (Real.exp_le_exp.mpr hLc))

theorem allocatedIdealCoverPrimitiveRadius_le {p c : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hq : Fintype.card α ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCc : ∀ j, C j ≤ Real.exp c) (j : Fin m) :
    allocatedIdealCoverPrimitiveRadius m p c ≤ allocatedIdealCoverRadius (G := G) B rowSets C j := by
  have h := allocatedComparisonDimensions_of_primitive (G := G) (α := α)
    (O := fun j => (rowSets j : Type _)) B
    (fun j => (Subtype.val : rowSets j → Finset α)) hq (fun _ => Subtype.val_injective) hp hvars hI hn
  have hpD := (allocatedComparisonDimension_bounds m hp).2.2.1
  have hi := allocatedIdealCoverRadius_inverse_from_dimensions B rowSets h hc
    (fun j => (hI j).trans hpD) (fun j => (hn j).trans hpD) C hC hCc j
  have hr := allocatedIdealCoverRadius_pos (G := G) B rowSets C hC j
  have hinv := (inv_le_inv₀ (Real.exp_pos (allocatedIdealCoverPrimitiveLog m p c)) (inv_pos.mpr hr)).2 hi
  simpa only [allocatedIdealCoverPrimitiveRadius, Real.exp_neg, inv_inv] using hinv

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem kernelOutputEnvelope_mono {D p D' p' : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hDD : D ≤ D') (hpp : p ≤ p') :
    kernelOutputEnvelope D p ≤ kernelOutputEnvelope D' p' := by
  have hD' : 0 ≤ D' := hD.trans hDD
  have hp' : 0 ≤ p' := hp.trans hpp
  have hi : kernelInverseEnvelope D p ≤ kernelInverseEnvelope D' p' := by
    unfold kernelInverseEnvelope
    gcongr
  have hg : kernelGeometryEnvelope D p ≤ kernelGeometryEnvelope D' p' := by
    unfold kernelGeometryEnvelope
    gcongr
  have hg0 := kernelGeometryEnvelope_nonneg hD hp
  unfold kernelOutputEnvelope
  gcongr

namespace VectorPolynomial

theorem allocatedJointLengthEnvelope_mono (m : ℕ) {D p e D' p' e' : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p)
    (hDD : D ≤ D') (hpp : p ≤ p') (hee : e ≤ e') :
    allocatedJointLengthEnvelope m D p e ≤ allocatedJointLengthEnvelope m D' p' e' := by
  have hD' : 0 ≤ D' := hD.trans hDD
  have hp' : 0 ≤ p' := hp.trans hpp
  have hi : kernelInverseEnvelope D p ≤ kernelInverseEnvelope D' p' := by
    unfold kernelInverseEnvelope
    gcongr
  have hk : allocatedKernelEnvelope m D p ≤ allocatedKernelEnvelope m D' p' := by
    unfold allocatedKernelEnvelope
    gcongr
  have ho := kernelOutputEnvelope_mono hD (show 0 ≤ 4 * (p + 8) by positivity)
    hDD (show 4 * (p + 8) ≤ 4 * (p' + 8) by linarith)
  have hd : allocatedDensityEnvelope m D p ≤ allocatedDensityEnvelope m D' p' := by
    unfold allocatedDensityEnvelope
    gcongr
  have hi0 := kernelInverseEnvelope_nonneg hD hp
  have hk0 : 0 ≤ allocatedKernelEnvelope m D p := by
    unfold allocatedKernelEnvelope
    positivity
  have hd0 := allocatedDensityEnvelope_nonneg m hD hp
  dsimp only [allocatedJointLengthEnvelope, allocatedFrontEnvelope,
    allocatedAccuracyEnvelope, allocatedTupleEnvelope]
  gcongr

theorem coefficientErrorAccuracyLog_mono {D e D' e' : ℝ}
    (hD : 0 ≤ D) (hDD : D ≤ D') (hee : e ≤ e') :
    coefficientErrorAccuracyLog D e ≤ coefficientErrorAccuracyLog D' e' := by
  have hD' : 0 ≤ D' := hD.trans hDD
  dsimp only [coefficientErrorAccuracyLog, coefficientErrorSpatialLog, coefficientMajorantMassLog,
    coefficientErrorVolumeLog, anisotropicSpatialCapLog]
  gcongr

theorem allocatedComparisonDimension_mono (m : ℕ) {p p' : ℝ}
    (hp : 0 ≤ p) (hpp : p ≤ p') :
    allocatedComparisonDimension m p ≤ allocatedComparisonDimension m p' := by
  unfold allocatedComparisonDimension
  gcongr

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

theorem allocatedIdealCoverRadius_half_le_physical
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (j : Fin m) :
    allocatedIdealCoverRadius (G := G) B rowSets C j / 2 ≤
      allocatedPhysicalChartRadius (G := G) B α C 1 j := by
  let N : ℝ := Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))
  let A : ℝ := (2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)
  let H := allocatedIdealCoverSupport (G := G) B rowSets j
  let D : ℝ := 4 * (C j + 1) * ((Fintype.card (I j) : ℝ) + 1)
  let r : ℝ := (rowSets j).card + 1
  let : Nonempty (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) :=
    ⟨⟨0, by simp⟩⟩
  have hN : 1 ≤ N := by
    dsimp only [N]
    exact_mod_cast Nat.succ_le_of_lt (Fintype.card_pos (α :=
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)))
  have hA : 0 < A := by dsimp [A]; positivity
  have hH : 0 ≤ H := allocatedIdealCoverSupport_nonneg B rowSets j
  have hNA : N * A ≤ H := allocatedIdealCoverSupport_inactive B rowSets j
  have hr : 1 ≤ r := by
    dsimp only [r]
    linarith [Nat.cast_nonneg (α := ℝ) (rowSets j).card]
  have hCj := hC j
  have hD : 0 < D := by dsimp [D]; positivity
  have hnum : (N + 1) * A ≤ 2 * (H + 1) := by nlinarith
  have hden : D * ((N + 1) * A) ≤ 2 * (D * r * (H + 1)) := by
    have hmul := mul_le_mul_of_nonneg_left hnum hD.le
    have hrow := mul_le_mul_of_nonneg_right hr (show 0 ≤ D * (H + 1) by positivity)
    nlinarith
  have hleft : 0 < D * r * (H + 1) := by positivity
  have hright : 0 < D * ((N + 1) * A) := by positivity
  have hi : 1 / (D * r * (H + 1)) ≤ 2 / (D * ((N + 1) * A)) :=
    (div_le_div_iff₀ hleft hright).mpr (by simpa only [one_mul] using hden)
  have hh : (1 / (D * r * (H + 1))) / 2 ≤ 1 / (D * ((N + 1) * A)) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hi
  convert hh using 1 <;>
    simp only [allocatedIdealCoverRadius, finiteRowChartRadius, allocatedPhysicalChartRadius,
      D, r, H, N, A, add_comm (1 : ℝ)] <;> ring

noncomputable def allocatedSourceCoverRadiusLog {A : Type*} [Semiring A]
    (m : ℕ) (p c : A) : A := allocatedIdealCoverPrimitiveLog m p c + 1

noncomputable def allocatedSourceCoverRadius (m : ℕ) (p c : ℝ) : ℝ :=
  Real.exp (-allocatedSourceCoverRadiusLog m p c)

theorem allocatedSourceCoverRadius_bounds {p c : ℝ} (hp : 0 ≤ p) (hc : 0 ≤ c) :
    0 ≤ allocatedSourceCoverRadiusLog m p c ∧
      0 < allocatedSourceCoverRadius m p c ∧ allocatedSourceCoverRadius m p c ≤ 1 ∧
      (allocatedSourceCoverRadius m p c)⁻¹ = Real.exp (allocatedSourceCoverRadiusLog m p c) ∧
      allocatedSourceCoverRadius m p c ≤ allocatedIdealCoverPrimitiveRadius m p c / 2 := by
  have hL := (allocatedIdealCoverPrimitiveRadius_bounds m hp hc).1
  have hlog : 0 ≤ allocatedSourceCoverRadiusLog m p c := by
    unfold allocatedSourceCoverRadiusLog
    linarith
  refine ⟨hlog, Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hlog), ?_, ?_⟩
  · simp only [allocatedSourceCoverRadius, Real.exp_neg, inv_inv]
  · apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ Real.exp (-allocatedSourceCoverRadiusLog m p c) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left htwo (Real.exp_pos _).le
      _ = allocatedIdealCoverPrimitiveRadius m p c := by
        rw [← Real.exp_add]
        unfold allocatedSourceCoverRadiusLog allocatedIdealCoverPrimitiveRadius
        congr 1
        ring

theorem allocatedSourceCoverRadius_le_charts {p c : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hq : Fintype.card α ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCc : ∀ j, C j ≤ Real.exp c) (j : Fin m) :
    allocatedSourceCoverRadius m p c ≤ allocatedPhysicalChartRadius (G := G) B α C 1 j ∧
      allocatedSourceCoverRadius m p c ≤ allocatedIdealCoverRadius (G := G) B rowSets C j := by
  have hhalf := (allocatedSourceCoverRadius_bounds (m := m) hp hc).2.2.2.2
  have hcover := allocatedIdealCoverPrimitiveRadius_le B rowSets hp hc hq hvars hI hn C hC hCc j
  have hsmall := hhalf.trans (div_le_div_of_nonneg_right hcover (by norm_num : (0 : ℝ) ≤ 2))
  refine ⟨hsmall.trans (allocatedIdealCoverRadius_half_le_physical B rowSets C hC j), ?_⟩
  have hpos := allocatedIdealCoverRadius_pos (G := G) B rowSets C hC j
  exact hsmall.trans (by linarith)

theorem allocatedSourceCoverRadiusLog_mono {p c p' c' : ℝ}
    (hp : 0 ≤ p) (hpp : p ≤ p') (hcc : c ≤ c') :
    allocatedSourceCoverRadiusLog m p c ≤ allocatedSourceCoverRadiusLog m p' c' := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  have hDD := allocatedComparisonDimension_mono m hp hpp
  unfold allocatedSourceCoverRadiusLog allocatedIdealCoverPrimitiveLog allocatedIdealCoverInputLog
    allocatedSiteCoefficientLog
  gcongr

theorem exists_allocatedSourceCoverRadiusLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {p c : ℝ}, 0 ≤ p → 0 ≤ c →
      allocatedSourceCoverRadiusLog m p c ≤ (p + c + a) ^ a := by
  let poly : Polynomial ℕ := allocatedSourceCoverRadiusLog m Polynomial.X Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p c hp hc
  apply (allocatedSourceCoverRadiusLog_mono hp (by linarith : p ≤ p + c)
    (by linarith : c ≤ p + c)).trans
  simpa [poly, allocatedSourceCoverRadiusLog, allocatedIdealCoverPrimitiveLog, allocatedIdealCoverInputLog,
    allocatedSiteCoefficientLog, allocatedComparisonDimension, Polynomial.eval₂_pow] using
    hbound (p + c) (add_nonneg hp hc)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem allocatedActualProfileFourier_nonneg (m : ℕ) {D p e g s : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (he : 0 ≤ e) (hg : 0 ≤ g) (hs : 0 ≤ s) :
    0 ≤ allocatedProfileFourierOutput (allocatedActualProfileInput m D p e g s) := by
  have hinput := (allocatedActualProfileInput_bounds m hD hp he hg hs).1
  have hlog := allocatedProfileErrorLog_nonneg hinput
  unfold allocatedProfileFourierOutput allocatedProfileFourierInput
  positivity

set_option maxHeartbeats 400000 in
theorem exists_allocatedActualProfileFourier_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {D p e g s : ℝ},
      0 ≤ D → 0 ≤ p → 0 ≤ e → 0 ≤ g → 0 ≤ s →
      allocatedProfileFourierOutput (allocatedActualProfileInput m D p e g s) ≤
        (D + p + e + g + s + a) ^ a := by
  let poly : Polynomial ℕ := allocatedProfileFourierOutput
    (allocatedActualProfileInput m Polynomial.X Polynomial.X Polynomial.X Polynomial.X Polynomial.X)
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro D p e g s hD hp he hg hs
  let R := D + p + e + g + s
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hDR : D ≤ R := by dsimp [R]; linarith
  have hpR : p ≤ R := by dsimp [R]; linarith
  have heR : e ≤ R := by dsimp [R]; linarith
  have hgR : g ≤ R := by dsimp [R]; linarith
  have hsR : s ≤ R := by dsimp [R]; linarith
  have hinput : allocatedActualProfileInput m D p e g s ≤
      allocatedActualProfileInput m R R R R R := by
    dsimp only [allocatedActualProfileInput, allocatedDensityEnvelope, allocatedProxyLipEnvelope,
      allocatedIdealLipEnvelope, kernelOutputEnvelope, kernelGeometryEnvelope, kernelInverseEnvelope]
    gcongr
  have hinput0 := (allocatedActualProfileInput_bounds m hD hp he hg hs).1
  have hinputR : 0 ≤ allocatedActualProfileInput m R R R R R := hinput0.trans hinput
  have hmono : allocatedProfileFourierOutput (allocatedActualProfileInput m D p e g s) ≤
      allocatedProfileFourierOutput (allocatedActualProfileInput m R R R R R) := by
    dsimp only [allocatedProfileFourierOutput, allocatedProfileFourierInput, allocatedProfileErrorLog,
      allocatedErrorKernelLog]
    gcongr
  apply hmono.trans
  simpa [poly, R, allocatedProfileFourierOutput, allocatedProfileFourierInput,
    allocatedProfileErrorLog, allocatedErrorKernelLog, allocatedActualProfileInput,
    allocatedDensityEnvelope, allocatedProxyLipEnvelope, allocatedIdealLipEnvelope,
    kernelOutputEnvelope, kernelGeometryEnvelope, kernelInverseEnvelope,
    Polynomial.eval₂_pow] using hbound R (by dsimp [R]; positivity)

theorem allocatedOriginalGeometryLog_nonneg (m : ℕ) {P p w v E : ℝ}
    (hP : 0 ≤ P) (hp : 0 ≤ p) (hw : 0 ≤ w) (hv : 0 ≤ v) (hE : 0 ≤ E) :
    0 ≤ allocatedOriginalGeometryLog m P p w v E := by
  have hshift := recenteredShiftLog_nonneg hP (by linarith : 0 ≤ P + 1)
  have hmass := allocatedSiteSpatialMassLog_nonneg (allocatedComparisonDimension_bounds m hp).1 hw hv
  unfold allocatedOriginalGeometryLog allocatedOriginalMassLog coefficientErrorVolumeLog
  positivity

theorem exists_allocatedOriginalGeometryLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {P p w v E : ℝ},
      0 ≤ P → 0 ≤ p → 0 ≤ w → 0 ≤ v → 0 ≤ E →
      allocatedOriginalGeometryLog m P p w v E ≤ (P + p + w + v + E + a) ^ a := by
  let poly : Polynomial ℕ := allocatedOriginalGeometryLog m
    Polynomial.X Polynomial.X Polynomial.X Polynomial.X Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro P p w v E hP hp hw hv hE
  let R := P + p + w + v + E
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hPR : P ≤ R := by dsimp [R]; linarith
  have hpR : p ≤ R := by dsimp [R]; linarith
  have hwR : w ≤ R := by dsimp [R]; linarith
  have hvR : v ≤ R := by dsimp [R]; linarith
  have hER : E ≤ R := by dsimp [R]; linarith
  have hmono : allocatedOriginalGeometryLog m P p w v E ≤
      allocatedOriginalGeometryLog m R R R R R := by
    dsimp only [allocatedOriginalGeometryLog, allocatedOriginalMassLog, allocatedSiteSpatialMassLog,
      allocatedComparisonDimension, recenteredShiftLog, coefficientErrorVolumeLog, anisotropicSpatialCapLog,
      spatialLipschitzEnvelope, spatialFixedProfileEnvelope, coefficientMajorantMassLog]
    gcongr
  apply hmono.trans
  simpa [poly, R, allocatedOriginalGeometryLog, allocatedOriginalMassLog,
    allocatedSiteSpatialMassLog, allocatedComparisonDimension, recenteredShiftLog,
    coefficientErrorVolumeLog, anisotropicSpatialCapLog, spatialLipschitzEnvelope,
    spatialFixedProfileEnvelope, coefficientMajorantMassLog, Polynomial.eval₂_pow] using
    hbound R (by dsimp [R]; positivity)

theorem exists_allocatedSiteFourier_total_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {p w v : ℝ}, 0 ≤ p → 0 ≤ w → 0 ≤ v →
      allocatedSiteErrorFourierOutput m p w v ≤ (p + w + v + a) ^ a := by
  obtain ⟨a, ha, hbound⟩ := exists_allocatedSiteErrorFourierOutput_bound m
  refine ⟨a, ha, ?_⟩
  intro p w v hp hw hv
  have hpR : p ≤ p + w + v := by linarith
  have hwR : w ≤ p + w + v := by linarith
  have hvR : v ≤ p + w + v := by linarith
  have hR : 0 ≤ p + w + v := by positivity
  apply le_trans ?_ (hbound (p + w + v) (by positivity))
  have hD := allocatedComparisonDimension_mono m hp hpR
  have hD0 := (allocatedComparisonDimension_bounds m hp).1
  have hDR := (allocatedComparisonDimension_bounds m hR).1
  have hT : allocatedSiteErrorPrimitiveLog m p w v ≤
      allocatedSiteErrorPrimitiveLog m (p + w + v) (p + w + v) (p + w + v) := by
    dsimp only [allocatedSiteErrorPrimitiveLog, allocatedErrorPrimitiveLog]
    gcongr
  have hT0 := (allocatedSiteErrorPrimitiveLog_bounds m hp hw hv).1
  have hTR := (allocatedSiteErrorPrimitiveLog_bounds m hR hR hR).1
  have hL : allocatedSiteErrorFourierInput m p w v ≤
      allocatedSiteErrorFourierInput m (p + w + v) (p + w + v) (p + w + v) := by
    dsimp only [allocatedSiteErrorFourierInput, allocatedErrorKernelLog]
    gcongr
  have hL0 := (allocatedSiteErrorFourier_budgets m hp hw hv).1
  have hLR := (allocatedSiteErrorFourier_budgets m hR hR hR).1
  dsimp only [allocatedSiteErrorFourierOutput]
  gcongr

end Erdos3.VectorPolynomial

end

end OAI
