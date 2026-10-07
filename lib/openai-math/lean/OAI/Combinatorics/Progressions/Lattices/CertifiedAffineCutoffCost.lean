/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateRealThreshold
import OAI.Combinatorics.Progressions.Geometry.CertifiedFullChartRecoveredTerminal
import OAI.Combinatorics.Progressions.Geometry.GlobalMarkedNativeChartResetConditions
import OAI.Combinatorics.Progressions.Lattices.FullTaggedAffineComplementAgreement
import OAI.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateSamplerFacts

namespace OAI

section

namespace Erdos3
open scoped Classical

theorem exists_weighted_common_real_grid_vector
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (outer : FiniteProbabilityWeights Ω) (S : Finset Ω) (hS : 0 < outer.mass S)
    (v : Ω → ι → ℝ) (l : ℕ) (hl : 0 < l) {B p : ℝ}
    (hp : 0 ≤ p) (hB : 0 ≤ B) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hlp : (l : ℝ) ≤ Real.exp p) (hBp : B ≤ Real.exp p)
    (hgrid : ∀ a ∈ S, v a ∈ realDenominatorGrid l)
    (hbound : ∀ a ∈ S, ∀ i, |v a i| ≤ B) :
    ∃ a₀ ∈ S, ∃ T : Finset Ω, T ⊆ S ∧ a₀ ∈ T ∧
      (∀ a ∈ T, v a = v a₀) ∧
      Real.exp (-((p + 3) ^ 3)) * outer.mass S ≤ outer.mass T := by
  let window : Set (ι → ℝ) :=
    {x | x ∈ realDenominatorGrid l ∧ ∀ i, |x i| ≤ B}
  obtain ⟨hfinite, hcard⟩ := finite_card_real_grid_window window l ⌈(l : ℝ) * B⌉₊ hl 0
    (fun _ hx => hx.1) (by intro x hx i; simpa only [Pi.zero_apply, sub_zero] using hx.2 i)
    (Nat.le_ceil _)
  have hcount : (window.ncard : ℝ) ≤ Real.exp ((p + 3) ^ 3) :=
    (Nat.cast_le.mpr hcard).trans (real_grid_window_count_le_exp _ _ hp hB hd hlp hBp)
  obtain ⟨c, _, T, hTS, hT, hc, hmass⟩ :=
    exists_weighted_exponential_constant_fiber outer S hS v window hfinite
      (fun a ha => ⟨hgrid a ha, hbound a ha⟩) hcount
  obtain ⟨a₀, ha₀⟩ := hT
  exact ⟨a₀, hTS ha₀, T, hTS, ha₀,
    fun a ha => (hc a ha).trans (hc a₀ ha₀).symm, hmass⟩

theorem exists_weighted_common_coordinate_grid_vector
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (outer : FiniteProbabilityWeights Ω) (S : Finset Ω) (hS : 0 < outer.mass S)
    (v : Ω → ι → ℝ) (den : ι → ℕ) (hden : ∀ i, 0 < den i) {p : ℝ}
    (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hdenp : ∀ i, (den i : ℝ) ≤ Real.exp p)
    (hgrid : ∀ a ∈ S, ∀ i, ∃ z : ℤ, (den i : ℝ) * v a i = z)
    (hbound : ∀ a ∈ S, ∀ i, |v a i| ≤ Real.exp p) :
    ∃ a₀ ∈ S, ∃ T : Finset Ω, T ⊆ S ∧ a₀ ∈ T ∧
      (∀ a ∈ T, v a = v a₀) ∧
      Real.exp (-((2 * p + 3) ^ 3)) * outer.mass S ≤ outer.mass T := by
  let scaled : Ω → ι → ℝ := fun a i => (den i : ℝ) * v a i
  have hscaled_grid (a) (ha : a ∈ S) : scaled a ∈ realDenominatorGrid 1 := by
    choose z hz using hgrid a ha
    refine ⟨z, ?_⟩
    funext i
    simpa only [Nat.cast_one, Pi.smul_apply, smul_eq_mul, one_mul] using (hz i).symm
  have hscaled_bound (a) (ha : a ∈ S) (i) : |scaled a i| ≤ Real.exp (2 * p) := by
    dsimp only [scaled]
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    calc
      _ ≤ Real.exp p * Real.exp p :=
        mul_le_mul (hdenp i) (hbound a ha i) (abs_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨a₀, ha₀, T, hTS, haT, hsame, hmass⟩ :=
    exists_weighted_common_real_grid_vector outer S hS scaled 1 (by omega)
      (by positivity : 0 ≤ 2 * p) (Real.exp_nonneg _) (hd.trans (by linarith))
      (by simpa only [Nat.cast_one] using Real.one_le_exp (by positivity : 0 ≤ 2 * p))
      le_rfl hscaled_grid hscaled_bound
  refine ⟨a₀, ha₀, T, hTS, haT, ?_, hmass⟩
  intro a ha
  funext i
  exact mul_left_cancel₀ (by exact_mod_cast (hden i).ne' : (den i : ℝ) ≠ 0)
    (congrFun (hsame a ha) i)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule _root_.MvPolynomial _root_.OAI.MvPolynomial BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_quotient_bound
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (j : Fin m) {T : Type*} (Q : (J j → ℝ) →ₗ[ℝ] (T → ℝ))
    (hQU : U j ≤ LinearMap.ker Q) {CQ : ℝ} (hCQ : 0 ≤ CQ)
    (hQ : ∀ x t, |Q x t| ≤ CQ * ‖x‖)
    (x : LayerSamplerVariables G I n B → ℝ)
    (hx : ∀ k, |x k| ≤ layerSamplerBox B U b S k) (t : T) :
    |Q (fun i => MvPolynomial.eval x (integerSampledRealChart
      (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample)
        (Sum.inr ⟨j, i⟩))) t| ≤
      CQ * (C j * (((Fintype.card (I j) : ℝ) + 1) * R j)) := by
  let mixed : J j → ℝ := fun i => mixedPolynomialPoint (euclideanSubspace (U j))
    (b j) (o j) Subtype.val (sample j).1 (sample j).2 x i
  let integer : J j → ℝ := fun i => MvPolynomial.eval x (integerSampledRealChart
    (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) (Sum.inr ⟨j, i⟩))
  have hrem : eval (fun z => (jointIntegerFrame (a, v) none z : ℝ) +
      ∑ k, (jointIntegerFrame (a, v) (some k) z : ℝ) * x k) (poly j) - (c j).val =
      mixed + integer := by
    funext i
    exact h.integerFullChart_remainder B U b hb o S hR hσ poly hm hp c a v sample read x j i
  have hretained : eval (fun z => (jointIntegerFrame (a, v) none z : ℝ) +
      ∑ k, (jointIntegerFrame (a, v) (some k) z : ℝ) * x k) (poly j) - (c j).val ∈ U j :=
    (U j).sub_mem ((eval_mem_iff_coefficients (U j) (poly j)).mpr (hm j) _) (c j).property
  have hsum : Q mixed + Q integer = 0 := by
    rw [← map_add, ← hrem]
    exact hQU hretained
  have hquotient : Q integer = -Q mixed := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_comm] using hsum
  have hnonneg : 0 ≤ C j * (((Fintype.card (I j) : ℝ) + 1) * R j) :=
    mul_nonneg (hC j) (mul_nonneg (by positivity) (hR j).le)
  have hnorm : ‖mixed‖ ≤ C j * (((Fintype.card (I j) : ℝ) + 1) * R j) := by
    apply (pi_norm_le_iff_of_nonneg hnonneg).mpr
    intro i
    simpa only [mixed, Real.norm_eq_abs] using
      allocatedLayerSupported_polynomial_bound B U b o hR hσ S hσ1 C hC hchart
        j (sample j) (h.2.2.1 j).2 x hx i
  change |Q integer t| ≤ _
  calc
    _ = |Q mixed t| := by rw [hquotient]; simp
    _ ≤ CQ * ‖mixed‖ := hQ mixed t
    _ ≤ _ := mul_le_mul_of_nonneg_left hnorm hCQ

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFrozenFullChart_anchor_bound
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (j : Fin m) {T : Type*} (Q : (J j → ℝ) →ₗ[ℝ] (T → ℝ))
    (hQU : U j ≤ LinearMap.ker Q) {CQ : ℝ} (hCQ : 0 ≤ CQ)
    (hQ : ∀ x t, |Q x t| ≤ CQ * ‖x‖)
    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, |(fixed i : ℝ)| ≤ layerSamplerBox B U b S i.val) (t : T) :
    |Q (fun i => MvPolynomial.eval (0 : {k // keep k} → ℝ) (integerSampledRealChart
      (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed)
        (Sum.inr ⟨j, i⟩))) t| ≤
      CQ * (C j * (((Fintype.card (I j) : ℝ) + 1) * R j)) := by
  have heval (i : J j) : MvPolynomial.eval (0 : {k // keep k} → ℝ)
      (integerSampledRealChart
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed)
          (Sum.inr ⟨j, i⟩)) =
      MvPolynomial.eval (finiteSplitPoint keep 0 (fun i => (fixed i : ℝ)))
        (integerSampledRealChart
          (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample)
            (Sum.inr ⟨j, i⟩)) := by
    change MvPolynomial.eval _ (integerSampledRealChart
      (fun z => freezePolynomial keep fixed
        (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)) _) = _
    rw [integerSampledRealChart_freeze, freezePolynomial_eval]
  simp_rw [heval]
  apply h.integerFullChart_quotient_bound B U b hb o S hR hσ poly hm hσ1 C hC hchart hp
    c a v sample read j Q hQU hCQ hQ _ _ t
  intro k
  by_cases hk : keep k
  · simpa [finiteSplitPoint, hk] using
      (zero_le_one.trans (layerSamplerBox_one_le B U b S k))
  · simpa [finiteSplitPoint, hk] using hfixed ⟨k, hk⟩

theorem allocatedFrozenIntegerFullChart_anchor_grid
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (j : Fin m) {T : Type*} (Q : (J j → ℝ) →ₗ[ℝ] (T → ℝ)) (D : ℝ)
    (hgrid : ∀ z : J j → ℤ, ∀ t, ∃ a : ℤ, D * Q (fun i => (z i : ℝ)) t = a)
    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬keep i} → ℤ) (t : T) :
    ∃ z : ℤ, D * Q (fun i => MvPolynomial.eval (0 : {k // keep k} → ℝ)
      (integerSampledRealChart
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed)
          (Sum.inr ⟨j, i⟩))) t = z := by
  have heval (i : J j) : MvPolynomial.eval (0 : {k // keep k} → ℝ)
      (integerSampledRealChart
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed)
          (Sum.inr ⟨j, i⟩)) =
      (MvPolynomial.eval (0 : {k // keep k} → ℤ)
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed
          (Sum.inr ⟨j, i⟩)) : ℝ) := by
    simpa only [Pi.zero_apply, Int.cast_zero, Pi.zero_def] using
      integerSampledRealChart_eval
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed)
        (0 : {k // keep k} → ℤ) (Sum.inr ⟨j, i⟩)
  simp_rw [heval]
  exact hgrid _ t

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem le_monomialScale_of_coordinate {A : Type*} (T : A → ℝ)
    (hT : ∀ i, 1 ≤ T i) {α : A →₀ ℕ} (i : A) (hi : α i ≠ 0) :
    T i ≤ monomialScale T α := by
  classical
  have hp : T i ≤ T i ^ α i := by
    simpa only [pow_one] using pow_le_pow_right₀ (hT i) (Nat.one_le_iff_ne_zero.mpr hi)
  have hs : ({i} : Finset A) ⊆ α.support :=
    Finset.singleton_subset_iff.mpr (Finsupp.mem_support_iff.mpr hi)
  have hprod := Finset.prod_le_prod_of_subset_of_one_le₀ hs
    (fun j _ => pow_nonneg (zero_le_one.trans (hT j)) (α j))
    (fun j _ _ => one_le_pow₀ (hT j))
  exact hp.trans (by
    simpa only [Finset.prod_singleton, monomialScale, Finsupp.prod] using hprod)

namespace VectorPolynomial
open Module Submodule _root_.MvPolynomial _root_.OAI.MvPolynomial BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_mixed_long_coeff
    (hσ1 : ∀ j, σ j ≤ 1)
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (j : Fin m) {T : Type*}
    (Q : (J j → ℝ) →ₗ[ℝ] (T → ℝ)) (hQU : U j ≤ LinearMap.ker Q)
    {C CQ D H : ℝ} (hC : 0 ≤ C) (hCQ : 0 ≤ CQ) (hD : 0 < D)
    (hchart : ∀ x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C * ‖x‖)
    (hQ : ∀ x t, |Q x t| ≤ CQ * ‖x‖)
    (hgrid : ∀ z : J j → ℤ, ∀ t, ∃ a : ℤ, D * Q (fun i => (z i : ℝ)) t = a)
    (hthreshold : CQ * (C * (((Fintype.card (I j) : ℝ) + 1) * R j)) * D < H)
    (α : LayerSamplerVariables G I n B →₀ ℕ)
    (htouches : ∃ i, H ≤ layerSamplerBox B U b S i ∧ α i ≠ 0) :
    Q (fun i => (((allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample
      (Sum.inr ⟨j, i⟩)).coeff α : ℤ) : ℝ)) = 0 := by
  by_cases hdegree : α.degree ≤ j.val + 1
  · let frame : Option (LayerSamplerVariables G I n B) → X → ℝ :=
      fun k z => (jointIntegerFrame (a, v) k z : ℝ)
    let d : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) :=
      ⟨α, hdegree⟩
    have hc : canonicalCoefficientSample U b hb o sample =
        QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (centeredAffineCoefficientArray U poly hm c frame) :=
      h.2.1.trans (affineSampleCoefficientTorus_subtractConstant U poly hm c frame)
    change Q (fun i => (((coefficientIntegerFloorPolynomial U b o sample
      (centeredAffineCoefficientArray U poly hm c frame) j i).coeff d.val : ℤ) : ℝ)) = 0
    apply canonicalCoefficientSample_floor_coeff_separate U b hb o sample _ hc j d Q hQU hD hgrid
    let M : ℝ := C * (((Fintype.card (I j) : ℝ) + 1) * R j)
    let scale : ℝ := monomialScale (layerSamplerBox B U b S) α
    have hscale : 0 < scale := monomialScale_pos _
      (fun i => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S i)) α
    have hM : 0 ≤ M := mul_nonneg hC (mul_nonneg (by positivity) (hR j).le)
    have hnorm : ‖fun i => mixedLiftCoefficient (euclideanSubspace (U j))
        (b j) (o j) (sample j) d i‖ ≤ M / scale := by
      apply (pi_norm_le_iff_of_nonneg (div_nonneg hM hscale.le)).mpr
      intro i
      simpa only [Real.norm_eq_abs] using
        allocatedLayerLiftCoefficient_radius_bound B U b hR hσ S hσ1 o j hC hchart
          (sample j) (h.2.2.1 j).2 d i
    have hscaleH : H ≤ scale := by
      obtain ⟨i, hi, hαi⟩ := htouches
      exact hi.trans (le_monomialScale_of_coordinate _ (layerSamplerBox_one_le B U b S) i hαi)
    intro t
    calc
      _ ≤ CQ * ‖fun i => mixedLiftCoefficient (euclideanSubspace (U j))
          (b j) (o j) (sample j) d i‖ := hQ _ t
      _ ≤ CQ * (M / scale) := mul_le_mul_of_nonneg_left hnorm hCQ
      _ = (CQ * M) / scale := (mul_div_assoc CQ M scale).symm
      _ < 1 / D := (div_lt_div_iff₀ hscale hD).mpr (by
        simpa only [one_mul] using hthreshold.trans_le hscaleH)
  · have hzero (i : J j) : (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample
        (Sum.inr ⟨j, i⟩)).coeff α = 0 :=
      coeff_eq_zero_of_totalDegree_lt ((allocatedRecoveredIntegerFullChart_tag_degree
        B U b o poly hm c a v sample j i).trans_lt (lt_of_not_ge hdegree))
    simp only [hzero, Int.cast_zero]
    exact map_zero Q

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_frozen_coeff
    (hσ1 : ∀ j, σ j ≤ 1)
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (j : Fin m) {T : Type*} (keep : LayerSamplerVariables G I n B → Prop)
    (Q : (J j → ℝ) →ₗ[ℝ] (T → ℝ)) (hQU : U j ≤ LinearMap.ker Q)
    {C CQ D H : ℝ} (hC : 0 ≤ C) (hCQ : 0 ≤ CQ) (hD : 0 < D)
    (hchart : ∀ x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C * ‖x‖)
    (hQ : ∀ x t, |Q x t| ≤ CQ * ‖x‖)
    (hgrid : ∀ z : J j → ℤ, ∀ t, ∃ a : ℤ, D * Q (fun i => (z i : ℝ)) t = a)
    (hlong : ∀ i, keep i → H ≤ layerSamplerBox B U b S i)
    (hthreshold : CQ * (C * (((Fintype.card (I j) : ℝ) + 1) * R j)) * D < H)
    (fixed : {i // ¬ keep i} → ℤ)
    (α : {i // keep i} →₀ ℕ) (hα : α ≠ 0) :
    Q (fun i => (MvPolynomial.map (Int.castRingHom ℝ)
      (freezePolynomial keep fixed (allocatedRecoveredIntegerFullChart B U b o poly hm
        c a v sample (Sum.inr ⟨j, i⟩)))).coeff α) = 0 := by
  apply frozenPolynomialFamily_coeff_mem _ keep fixed (LinearMap.ker Q) _ α hα
  intro d hd
  apply h.integerFullChart_mixed_long_coeff B U b hb o S hR hσ poly hm hσ1 c a v sample read
    j Q hQU hC hCQ hD hchart hQ hgrid hthreshold d
  obtain ⟨i, hi, hdi⟩ := hd
  exact ⟨i, hlong i hi, hdi⟩

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_frozen_affine_range
    (hσ1 : ∀ j, σ j ≤ 1)
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (j : Fin m) {T : Type*} (keep : LayerSamplerVariables G I n B → Prop)
    (Q : (J j → ℝ) →ₗ[ℝ] (T → ℝ)) (hQU : U j ≤ LinearMap.ker Q)
    (Ktarget : Submodule ℝ (J j → ℝ)) (hker : LinearMap.ker Q ≤ Ktarget)
    {C CQ D H : ℝ} (hC : 0 ≤ C) (hCQ : 0 ≤ CQ) (hD : 0 < D)
    (hchart : ∀ x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C * ‖x‖)
    (hQ : ∀ x t, |Q x t| ≤ CQ * ‖x‖)
    (hgrid : ∀ z : J j → ℤ, ∀ t, ∃ a : ℤ, D * Q (fun i => (z i : ℝ)) t = a)
    (hlong : ∀ i, keep i → H ≤ layerSamplerBox B U b S i)
    (hthreshold : CQ * (C * (((Fintype.card (I j) : ℝ) + 1) * R j)) * D < H)
    (fixed : {i // ¬ keep i} → ℤ) (x : {i // keep i} → ℝ) :
    (fun i =>
      MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ)
        (freezePolynomial keep fixed (allocatedRecoveredIntegerFullChart B U b o poly hm
          c a v sample (Sum.inr ⟨j, i⟩)))) -
      MvPolynomial.eval 0 (MvPolynomial.map (Int.castRingHom ℝ)
        (freezePolynomial keep fixed (allocatedRecoveredIntegerFullChart B U b o poly hm
          c a v sample (Sum.inr ⟨j, i⟩))))) ∈ Ktarget := by
  apply hker
  apply polynomialFamily_eval_sub_zero_mem _ (LinearMap.ker Q) _ x
  exact h.integerFullChart_frozen_coeff B U b hb o S hR hσ poly hm hσ1 c a v sample read
    j keep Q hQU hC hCQ hD hchart hQ hgrid hlong hthreshold fixed

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule _root_.MvPolynomial _root_.OAI.MvPolynomial BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_certified_frozen_affine_range
    (hσ1 : ∀ j, σ j ≤ 1)
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (K : Set ((X ⊕ (Σ j, J j)) → ℝ)) {Bstage p M H : ℝ} {blocks : ℕ}
    (hcertificate : RationalTaggedConstraintCertificate J Set.univ K Bstage blocks)
    (hretained : ∀ t, (∀ j, (fun i => t (Sum.inr ⟨j, i⟩)) ∈ U j) → t ∈ K)
    (hp : 0 ≤ p) (hBp : Bstage ≤ p) (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hM : 0 ≤ M) (hcap : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ M)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hlong : ∀ i, keep i → H ≤ layerSamplerBox B U b S i)
    (hthreshold : Real.exp ((p + 2) ^ 9) ^ 2 * M < H)
    (fixed : {i // ¬ keep i} → ℤ) (x : {i // keep i} → ℝ) :
    (fun i => MvPolynomial.eval x
      (integerSampledRealChart
        (fun z => freezePolynomial keep fixed
          (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)) i) -
      MvPolynomial.eval 0
      (integerSampledRealChart
        (fun z => freezePolynomial keep fixed
          (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)) i)) ∈ K := by
  obtain ⟨cs, _, hbudget, hK⟩ := hcertificate
  rw [hK]
  refine ⟨Set.mem_univ _, ?_⟩
  intro constraint hc
  have hspan : U constraint.tag ≤
      span ℝ (Set.range (fun q i => (constraint.generators q i : ℝ))) := by
    apply constraint.retained_le_span U hretained
    intro point hpoint
    rw [hK] at hpoint
    exact hpoint.2 constraint hc
  obtain ⟨d, _, Q, hker, hQ, D, hD, hDbound, hgrid⟩ :=
    exists_rationalTaggedSpanProjection constraint.generators hp (hJ constraint.tag)
      ((hbudget constraint hc).1.trans hBp)
      (fun q i => ((hbudget constraint hc).2 q i).trans hBp)
  have hQU : U constraint.tag ≤ LinearMap.ker Q := by
    rw [hker]
    exact hspan
  have hgrid' : ∀ z : J constraint.tag → ℤ, ∀ t,
      ∃ a : ℤ, (D : ℝ) * Q (fun i => (z i : ℝ)) t = a := by
    intro z t
    obtain ⟨w, hw⟩ := hgrid z
    exact ⟨w t, (hw t).symm⟩
  have hnumeric : Real.exp ((p + 2) ^ 9) *
      (C constraint.tag * (((Fintype.card (I constraint.tag) : ℝ) + 1) * R constraint.tag)) *
        (D : ℝ) < H := by
    have hE := Real.exp_nonneg ((p + 2) ^ 9)
    calc
      _ ≤ Real.exp ((p + 2) ^ 9) * M * (D : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hcap constraint.tag) hE)
          (Nat.cast_nonneg D)
      _ ≤ Real.exp ((p + 2) ^ 9) * M * Real.exp ((p + 2) ^ 9) :=
        mul_le_mul_of_nonneg_left hDbound (mul_nonneg hE hM)
      _ = Real.exp ((p + 2) ^ 9) ^ 2 * M := by ring
      _ < H := hthreshold
  exact h.integerFullChart_frozen_affine_range B U b hb o S hR hσ poly hm hσ1 c a v sample read
    constraint.tag keep Q hQU _ (le_of_eq hker) (hC constraint.tag)
    (Real.exp_nonneg _) (by exact_mod_cast hD) (hchart constraint.tag) hQ hgrid'
    hlong hnumeric fixed x

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalLocalChart
variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

noncomputable def tagAnchor (j : Fin m) : J j → ℝ :=
  fun i => MvPolynomial.eval (0 : C.Variables → ℝ)
    (integerSampledRealChart C.integerChart (Sum.inr ⟨j, i⟩))

theorem fixed_abs_le_box (i : {i // ¬C.keep i}) :
    |(C.fixed i : ℝ)| ≤ layerSamplerBox B U b S i.val := by
  rw [abs_of_nonneg (by exact_mod_cast (C.fixed_in_box i).1),
    allocatedParameterBox_side_eq B U b S]
  exact_mod_cast (C.fixed_in_box i).2.le

theorem tagAnchor_quotient_bound
    (hσone : ∀ j, σ j ≤ 1) (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (j : Fin m) {T : Type*} (Q : (J j → ℝ) →ₗ[ℝ] (T → ℝ))
    (hQU : U j ≤ LinearMap.ker Q) {CQ : ℝ} (hCQ : 0 ≤ CQ)
    (hQ : ∀ x i, |Q x i| ≤ CQ * ‖x‖) (i : T) :
    |Q (C.tagAnchor j) i| ≤ CQ * (Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j)) :=
  C.recovered.integerFrozenFullChart_anchor_bound B U b hb o S hR hσ poly hm
    hσone Cgeo hCgeo hchart hp C.centerLift C.path.1.val C.path.2.val C.sample C.read
    j Q hQU hCQ hQ C.keep C.fixed C.fixed_abs_le_box i

theorem tagAnchor_quotient_grid
    (j : Fin m) {T : Type*} (Q : (J j → ℝ) →ₗ[ℝ] (T → ℝ)) (den : ℕ)
    (hgrid : ∀ z : J j → ℤ, ∀ i, ∃ a : ℤ, (den : ℝ) * Q (fun i => (z i : ℝ)) i = a)
    (i : T) : ∃ a : ℤ, (den : ℝ) * Q (C.tagAnchor j) i = a :=
  allocatedFrozenIntegerFullChart_anchor_grid B U b o poly hm
    C.centerLift C.path.1.val C.path.2.val C.sample j Q (den : ℝ) hgrid C.keep C.fixed i

end AllocatedExternalLocalChart

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

theorem exists_common_affine_anchor_refinement
    (Q : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (den : Fin m → ℕ)
    (hden : ∀ j, 0 < den j) {p : ℝ} (hp : 0 ≤ p)
    (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hdenp : ∀ j, (den j : ℝ) ≤ Real.exp p)
    (hgrid : ∀ j (z : J j → ℤ) i, ∃ a : ℤ, (den j : ℝ) * Q j (fun i => (z i : ℝ)) i = a)
    (hbound : ∀ z : P.productive, ∀ j i,
      |Q j ((P.chart z).tagAnchor j) i| ≤ Real.exp p)
    (hmass : 0 < massThreshold) :
    ∃ (c : ∀ j, J j → ℝ)
      (refinement : P.Refinement cost
        (Real.exp (-((2*p+3)^3)) * massThreshold) scoreThreshold),
      (∀ j i, |c j i| ≤ Real.exp p) ∧
      (∀ j i, ∃ a : ℤ, (den j : ℝ) * c j i = a) ∧
      (∀ z : refinement.problem.productive, ∀ j,
        Q j ((refinement.problem.chart z).tagAnchor j) = c j) ∧
      (∀ z : refinement.problem.productive,
        (refinement.problem.chart z).slice.integerPoints =
          (P.chart ⟨z.val, refinement.subset z.property⟩).slice.integerPoints) := by
  let v (a : A.Path) : (Σ j, J j) → ℝ :=
    if ha : a ∈ P.productive then fun i => Q i.1 ((P.chart ⟨a,ha⟩).tagAnchor i.1) i.2
    else 0
  have hv (z : P.productive) (i : Σ j, J j) :
      v z.val i = Q i.1 ((P.chart z).tagAnchor i.1) i.2 := by
    simp only [v, dite_eq_left z.property]
  obtain ⟨a₀, ha₀, retained, hsub, haT, hsame, hmassT⟩ :=
    exists_weighted_common_coordinate_grid_vector A.law P.productive (hmass.trans_le P.mass)
      v (fun i => den i.1) (fun i => hden i.1) hp hdim (fun i => hdenp i.1)
      (by
        intro a ha i
        rw [hv ⟨a,ha⟩]
        exact (P.chart ⟨a,ha⟩).tagAnchor_quotient_grid i.1 (Q i.1) (den i.1) (hgrid i.1) i.2)
      (by intro a ha i; rw [hv ⟨a,ha⟩]; exact hbound ⟨a,ha⟩ i.1 i.2)
  let refinement : P.Refinement cost
      (Real.exp (-((2*p+3)^3)) * massThreshold) scoreThreshold :=
    { retained := retained
      subset := hsub
      mass := (mul_le_mul_of_nonneg_left P.mass (Real.exp_nonneg _)).trans hmassT
      cost_le := le_rfl
      step := fun z => (P.chart ⟨z.val,hsub z.property⟩).step
      step_pos := fun z => (P.chart ⟨z.val,hsub z.property⟩).step_pos
      slice := fun z => (P.chart ⟨z.val,hsub z.property⟩).slice
      dense := fun z => (P.chart ⟨z.val,hsub z.property⟩).dense
      inside := fun _ => Finset.Subset.refl _
      scoreLower := fun z => P.score ⟨z.val,hsub z.property⟩ }
  refine ⟨fun j i => v a₀ ⟨j,i⟩, refinement, ?_, ?_, ?_, ?_⟩
  · intro j i
    change |v a₀ ⟨j,i⟩| ≤ Real.exp p
    rw [hv ⟨a₀,ha₀⟩ ⟨j,i⟩]
    exact hbound ⟨a₀,ha₀⟩ j i
  · intro j i
    change ∃ a : ℤ, (den j : ℝ) * v a₀ ⟨j,i⟩ = a
    rw [hv ⟨a₀,ha₀⟩ ⟨j,i⟩]
    exact (P.chart ⟨a₀,ha₀⟩).tagAnchor_quotient_grid j (Q j) (den j) (hgrid j) i
  · intro z j
    funext i
    change Q j ((P.chart ⟨z.val,hsub z.property⟩).tagAnchor j) i = v a₀ ⟨j,i⟩
    exact (hv ⟨z.val,hsub z.property⟩ ⟨j,i⟩).symm.trans
      (congrFun (hsame z.val z.property) ⟨j,i⟩)
  · intro z
    rfl

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalLocalChart
variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

theorem tag_values_sub_anchor_mem
    (hσone : ∀ j, σ j ≤ 1)
    (K : Set ((X ⊕ (Σ j, J j)) → ℝ)) {p Mbound H : ℝ} {blocks : ℕ}
    (hcertificate : RationalTaggedConstraintCertificate J Set.univ K p blocks)
    (hretained : ∀ t, (∀ j, (fun i => t (Sum.inr ⟨j, i⟩)) ∈ U j) → t ∈ K)
    (hp : 0 ≤ p) (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hM : 0 ≤ Mbound)
    (hcap : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ Mbound)
    (hlong : ∀ i, C.keep i → H ≤ layerSamplerBox B U b S i)
    (hthreshold : Real.exp ((p + 2) ^ 9) ^ 2 * Mbound < H)
    (x : C.Variables → ℝ) :
    (fun i => MvPolynomial.eval x (integerSampledRealChart C.integerChart i) -
      MvPolynomial.eval 0 (integerSampledRealChart C.integerChart i)) ∈ K :=
  C.recovered.integerFullChart_certified_frozen_affine_range B U b hb o S hR hσ poly hm
    hσone C.centerLift C.path.1.val C.path.2.val C.sample C.read K hcertificate hretained
    hp le_rfl hJ Cgeo hCgeo hchart hM hcap C.keep hlong hthreshold C.fixed x

end AllocatedExternalLocalChart

omit [Fintype X] [∀ j, Fintype (J j)]
  [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
theorem retained_tag_le_of_product_constraint
    (K : Set ((X ⊕ (Σ j, J j)) → ℝ))
    (V : ∀ j, Submodule ℝ (J j → ℝ))
    (hK : K = {t | ∀ j, (fun i => t (Sum.inr ⟨j,i⟩)) ∈ V j})
    (hretained : ∀ t, (∀ j, (fun i => t (Sum.inr ⟨j,i⟩)) ∈ U j) → t ∈ K)
    (j : Fin m) : U j ≤ V j := by
  intro x hx
  let t : X ⊕ (Σ k, J k) → ℝ :=
    Sum.elim (fun _ => 0) (fun i => (Pi.single j x : ∀ k, J k → ℝ) i.1 i.2)
  have ht : ∀ k, (fun i => t (Sum.inr ⟨k,i⟩)) ∈ U k := by
    intro k
    by_cases hk : k = j
    · subst k
      simpa only [t, Sum.elim_inr, Pi.single_eq_same] using hx
    · simpa only [t, Sum.elim_inr, Pi.single_eq_of_ne hk, Pi.zero_apply, Pi.zero_def] using (U k).zero_mem
  have htK := hretained t ht
  rw [hK] at htK
  simpa only [t, Sum.elim_inr, Pi.single_eq_same] using htK j

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration
open scoped BigOperators Classical TensorProduct

noncomputable def certifiedAffineCenterBudget (p : ℝ) : ℝ :=
  let q := p + ((p+2)^2+2)^63
  2*p + (q+2)^10 + (q+2)^8 + 1

private theorem affineCenterBudget_arithmetic {p a b : ℝ}
    (hp : 0 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 2*p+a+b+1 ∧ p ≤ 2*p+a+b+1 ∧ a ≤ 2*p+a+b+1 ∧
      2*p+b+1 ≤ 2*p+a+b+1 := by
  constructor
  · linarith only [hp, ha, hb]
  constructor
  · linarith only [hp, ha, hb]
  constructor <;> linarith only [hp, ha, hb]

private theorem affineCenterBudget_exp {p b : ℝ} :
    Real.exp (p+b+1) * Real.exp p = Real.exp (2*p+b+1) := by
  rw [← Real.exp_add]
  congr 1
  ring

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

structure CertifiedAffineRefinement
    (K : Set ((X ⊕ (Σ j, J j)) → ℝ)) (p : ℝ) where
  space : ∀ j, Submodule ℚ (J j → ℚ)
  projection : ∀ j, Matrix (J j) (J j) ℚ
  denominator : Fin m → ℕ
  constraint : K = {t | ∀ j, (fun i => t (Sum.inr ⟨j,i⟩)) ∈ realRationalCoordinateSpan (space j)}
  range_eq : ∀ j, LinearMap.range (fullTaggedRealMatrixProjection J projection j) =
    realRationalCoordinateSpan (space j)
  fixes_space : ∀ j x, x ∈ realRationalCoordinateSpan (space j) →
    fullTaggedRealMatrixProjection J projection j x = x
  projection_height : ∀ j i a, rationalLogHeight (projection j i a) ≤
    ((p + ((p+2)^2+2)^63) + 2)^8
  denominator_pos : ∀ j, 0 < denominator j
  denominator_bound : ∀ j, (denominator j : ℝ) ≤ Real.exp (certifiedAffineCenterBudget p)
  projection_grid : ∀ j i a, ∃ z : ℤ, (denominator j : ℝ) * (projection j i a : ℝ) = z
  translate : ∀ j, J j → ℝ
  translate_bound : ∀ j i, |translate j i| ≤ Real.exp (certifiedAffineCenterBudget p)
  translate_grid : ∀ j i, ∃ z : ℤ, (denominator j : ℝ) * translate j i = z
  translate_fixed : ∀ j, rationalTagProjectionComplement (projection j) (translate j) = translate j
  refinement : P.Refinement cost
    (Real.exp (-((2*certifiedAffineCenterBudget p+3)^3)) * massThreshold) scoreThreshold
  slice_points : ∀ z : refinement.problem.productive,
    (refinement.problem.chart z).slice.integerPoints =
      (P.chart ⟨z.val, refinement.subset z.property⟩).slice.integerPoints
  chart_fixed : ∀ z : refinement.problem.productive, ∀ x : (refinement.problem.chart z).Variables → ℝ,
    (fun v => MvPolynomial.eval
      (fun i => MvPolynomial.eval x (integerSampledRealChart (refinement.problem.chart z).integerChart i))
      (fullTaggedAffineMapChart J (fullTaggedRealMatrixProjection J projection) translate v)) =
      (fun i => MvPolynomial.eval x (integerSampledRealChart (refinement.problem.chart z).integerChart i))

theorem exists_certifiedAffineRefinement
    (hσone : ∀ j, σ j ≤ 1)
    (K : Set ((X ⊕ (Σ j, J j)) → ℝ)) {p H : ℝ} {blocks : ℕ}
    (hcertificate : RationalTaggedConstraintCertificate J Set.univ K p blocks)
    (hretained : ∀ t, (∀ j, (fun i => t (Sum.inr ⟨j, i⟩)) ∈ U j) → t ∈ K)
    (hp : 0 ≤ p) (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hblocks : (blocks : ℝ) ≤ p)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hcap : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ Real.exp p)
    (hlong : ∀ z : P.productive, ∀ i, (P.chart z).keep i → H ≤ layerSamplerBox B U b S i)
    (hthreshold : Real.exp ((p + 2) ^ 9) ^ 2 * Real.exp p < H)
    (hmass : 0 < massThreshold) : Nonempty (P.CertifiedAffineRefinement K p) := by
  let q := p + ((p+2)^2+2)^63
  let labelBudget := certifiedAffineCenterBudget p
  have hlabel : labelBudget = 2*p+(q+2)^10+(q+2)^8+1 := rfl
  have hbudget := affineCenterBudget_arithmetic hp
    (show 0 ≤ (q+2)^10 from by positivity) (show 0 ≤ (q+2)^8 from by positivity)
  have hlabel0 : 0 ≤ labelBudget := hlabel.symm ▸ hbudget.1
  have hplabel : p ≤ labelBudget := hlabel.symm ▸ hbudget.2.1
  have hdenlabel : (q+2)^10 ≤ labelBudget := hlabel.symm ▸ hbudget.2.2.1
  have hdimj (j : Fin m) : (Fintype.card (J j) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (Fintype.card_le_of_injective (Sigma.mk j) (by intro a b h; cases h; rfl))).trans hdim
  obtain ⟨V, projection, den, hK, hP⟩ :=
    hcertificate.exists_bounded_rational_retractions J hp hdimj hblocks
  let Q := fun j => rationalTagProjectionComplement (projection j)
  have hQU (j : Fin m) : U j ≤ LinearMap.ker (Q j) := by
    rw [rationalTagProjectionComplement_ker (projection j) (V j) (hP j).1 (hP j).2.1]
    exact retained_tag_le_of_product_constraint K (fun j => realRationalCoordinateSpan (V j)) hK hretained j
  have hgrid (j : Fin m) (z : J j → ℤ) (i : J j) :
      ∃ a : ℤ, (den j : ℝ) * Q j (fun i => (z i : ℝ)) i = a := by
    obtain ⟨a, ha⟩ := rationalTagProjectionComplement_integer_grid (projection j) (den j)
      (hP j).2.2.2.2.2.1 z
    exact ⟨a i, ha i⟩
  have hbound (z : P.productive) (j : Fin m) (i : J j) :
      |Q j ((P.chart z).tagAnchor j) i| ≤ Real.exp labelBudget := by
    have hraw := (P.chart z).tagAnchor_quotient_bound hσone Cgeo hCgeo hchart hpoly
      j (Q j) (hQU j) (Real.exp_nonneg (p+(q+2)^8+1))
      (rationalTagProjectionComplement_coordinate_exp_bound (projection j) hp
        (by positivity : 0 ≤ (q+2)^8) (hdimj j) (hP j).2.2.1) i
    calc
      _ ≤ Real.exp (p+(q+2)^8+1) *
          (Cgeo j * (((Fintype.card (I j) : ℝ)+1)*R j)) := hraw
      _ ≤ Real.exp (p+(q+2)^8+1) * Real.exp p :=
        mul_le_mul_of_nonneg_left (hcap j) (Real.exp_nonneg _)
      _ = Real.exp (2*p+(q+2)^8+1) := affineCenterBudget_exp
      _ ≤ Real.exp labelBudget := Real.exp_le_exp.mpr (hlabel.symm ▸ hbudget.2.2.2)
  obtain ⟨c, refinement, hcBound, hcGrid, hc, hpoints⟩ :=
    P.exists_common_affine_anchor_refinement Q den (fun j => (hP j).2.2.2.1)
      hlabel0 (hdim.trans hplabel)
      (fun j => (hP j).2.2.2.2.1.trans (Real.exp_le_exp.mpr hdenlabel))
      hgrid hbound hmass
  have hnonempty : refinement.problem.productive.Nonempty := by
    apply Finset.nonempty_of_ne_empty
    intro he
    have h := refinement.mass
    change Real.exp (-((2*labelBudget+3)^3)) * massThreshold ≤
      A.law.mass refinement.problem.productive at h
    rw [he] at h
    have hpos : 0 < Real.exp (-((2*labelBudget+3)^3)) * massThreshold :=
      mul_pos (Real.exp_pos _) hmass
    simpa [FiniteProbabilityWeights.mass] using hpos.trans_le h
  obtain ⟨z₀,hz₀⟩ := hnonempty
  have hcFixed (j : Fin m) : Q j (c j) = c j := by
    rw [← hc ⟨z₀,hz₀⟩ j]
    exact rationalTagProjectionComplement_idempotent (projection j) (V j)
      (hP j).1 (hP j).2.1 _
  refine ⟨{
    space := V
    projection := projection
    denominator := den
    constraint := hK
    range_eq := fun j => (hP j).1
    fixes_space := fun j => (hP j).2.1
    projection_height := fun j => (hP j).2.2.1
    denominator_pos := fun j => (hP j).2.2.2.1
    denominator_bound := fun j => (hP j).2.2.2.2.1.trans (Real.exp_le_exp.mpr hdenlabel)
    projection_grid := fun j => (hP j).2.2.2.2.2.1
    translate := c
    translate_bound := hcBound
    translate_grid := hcGrid
    translate_fixed := hcFixed
    refinement := refinement
    slice_points := hpoints
    chart_fixed := ?_ }⟩
  intro z x
  apply fullTaggedAffineMatrixChart_eval_eq_of_anchor J projection c
    (refinement.problem.chart z).tagAnchor _ ?_ (hc z) hcFixed
  intro j
  have hkeep (i) (hi : (refinement.problem.chart z).keep i) : H ≤ layerSamplerBox B U b S i :=
    hlong ⟨z.val,refinement.subset z.property⟩ i hi
  have hrange := (refinement.problem.chart z).tag_values_sub_anchor_mem hσone K
    hcertificate hretained hp hdimj Cgeo hCgeo hchart (Real.exp_nonneg _) hcap hkeep hthreshold x
  rw [hK] at hrange
  have hmem := hrange j
  rw [← rationalTagProjectionComplement_ker (projection j) (V j) (hP j).1 (hP j).2.1] at hmem
  exact hmem

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration
open scoped BigOperators Classical TensorProduct
attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  symbolPointwiseSubalgebra realificationLieSubalgebra

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

namespace CertifiedAffineRefinement
variable {P} {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p : ℝ}
    (Raff : P.CertifiedAffineRefinement K p)
    {κ : Type*} (cF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (cF '' {i | j ≤ ν i}))
    {W : LieSubalgebra ℚ Fmark.AssociatedGraded}
    {EF RF : Fmark.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
    (factors : GlobalMarkedNativeFactors Fmark cF ν hF (fullTaggedVariableWeight J) W
      (Fmark.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
        (fullTaggedVariableWeight J)
        (fullTaggedAffineMapChart J (fullTaggedRealMatrixProjection J Raff.projection) Raff.translate)
        (fullTaggedAffineMapChart_support J _ Raff.translate)
        (Fmark.realification.polynomialOrbitCoordinates _ marked)) EF RF)
    (z : Raff.refinement.problem.productive)

theorem actual_chart_product :
    let C := Raff.refinement.problem.chart z
    let pull := Fmark.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
      (fun _ : C.Variables => 1) (integerSampledRealChart C.integerChart) C.integerChart_support
    pull factors.left * pull factors.middle * pull factors.right =
      pull (Fmark.realification.polynomialOrbitCoordinates _ marked) := by
  dsimp only
  rw [← map_mul, ← map_mul, factors.product]
  exact Fmark.weightedAdaptedRealChartHom_eq_of_fixed_chart _ _ _ _ _ _
    (Raff.chart_fixed z) _

theorem actual_chart_native_conditions :
    let C := Raff.refinement.problem.chart z
    let pull := Fmark.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
      (fun _ : C.Variables => 1) (integerSampledRealChart C.integerChart) C.integerChart_support
    let residual := (pull factors.left)⁻¹ *
      pull (Fmark.realification.polynomialOrbitCoordinates _ marked) * (pull factors.right)⁻¹
    (Fmark.realPolynomialSymbolHom cF ν hF (fun _ : C.Variables => 1) residual).coord ∈
      realificationLieSubalgebra
        (Fmark.symbolPointwiseSubalgebra cF ν hF (fun _ : C.Variables => 1) W) ∧
    coefficients (residual.coord : VectorPolynomial C.Variables ℚ (ℝ ⊗[ℚ] M)) 0 ∈
      Fmark.realGradedRefiltrationLayer W 1 := by
  exact factors.fixed_chart_native_conditions
    (integerSampledRealChart (Raff.refinement.problem.chart z).integerChart)
    (Raff.refinement.problem.chart z).integerChart_support (Raff.chart_fixed z)

theorem actual_chart_right_grid {q : ℕ}
    (hgrid : Fmark.PolynomialRationalGrid cF (fullTaggedVariableWeight J) q factors.right) :
    let C := Raff.refinement.problem.chart z
    Fmark.PolynomialRationalGrid cF (fun _ : C.Variables => 1) q
      (Fmark.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
        (fun _ : C.Variables => 1) (integerSampledRealChart C.integerChart)
        C.integerChart_support factors.right) := by
  exact Fmark.polynomialRationalGrid_integerChart cF _ _
    (Raff.refinement.problem.chart z).integerChart
    (Raff.refinement.problem.chart z).integerChart_support q factors.right hgrid

end CertifiedAffineRefinement
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_certifiedAffineCenterBudget_power :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      certifiedAffineCenterBudget p + (2*certifiedAffineCenterBudget p+3)^3 +
        (2*(p+2)^9+p+2) ≤ (p+C)^C := by
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + ((X+2)^2+2)^63
  let L := 2*X+(Q+2)^10+(Q+2)^8+1
  let cost := L + (2*L+3)^3 + (2*(X+2)^9+X+2)
  obtain ⟨C,hC,hcost⟩ := exists_natPolynomial_eval_budget cost
  refine ⟨C,hC,?_⟩
  intro p hp
  simpa only [cost, L, Q, X, certifiedAffineCenterBudget,
    Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_ofNat, Polynomial.eval₂_one] using hcost p hp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem candidateSideCutoffCost_exp_bound {p : ℝ} (hp : 0 ≤ p) :
    candidateSideCutoffCost (Real.exp p) ≤ p+2 := by
  have hside := candidateSideCutoff_pos (Real.exp p)
  rw [candidateSideCutoffCost, max_eq_left hside]
  apply (Real.log_le_iff_le_exp (Nat.cast_pos.mpr hside)).mpr
  have hcut := candidateSideCutoff_lt_max_add_two (Real.exp p)
  rw [max_eq_left (Real.exp_nonneg _)] at hcut
  have hlarge := Real.one_le_exp hp
  calc
    _ ≤ Real.exp p + 2 := hcut.le
    _ ≤ 3 * Real.exp p := by linarith only [hlarge]
    _ ≤ Real.exp 2 * Real.exp p :=
      mul_le_mul_of_nonneg_right (by linarith only [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
    _ = Real.exp (p+2) := by rw [← Real.exp_add, add_comm]

theorem candidateSideCutoffCost_canonical_affine {p : ℝ} (hp : 0 ≤ p) :
    candidateSideCutoffCost (Real.exp ((p+2)^9)^2 * Real.exp p) ≤
      2*(p+2)^9+p+2 := by
  have heq : Real.exp ((p+2)^9)^2 * Real.exp p = Real.exp (2*(p+2)^9+p) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    norm_num only [Nat.cast_ofNat]
  rw [heq]
  exact candidateSideCutoffCost_exp_bound (by positivity)

end Erdos3.VectorPolynomial

end

end OAI
