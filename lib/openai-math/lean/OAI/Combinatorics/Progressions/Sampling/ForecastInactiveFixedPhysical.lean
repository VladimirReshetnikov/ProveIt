/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Lattices.ForecastInactiveAffineIntervalFixedResidueSite

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

universe u v w

variable {A : Type u} {S : Type v} [Fintype A] [Fintype S]
variable (e : A → ScalarSiteExpansion.{v,w} S)

noncomputable def forecastSiteFamilyRescale (r : A → ℝ) :
    A → ScalarSiteExpansion.{v,w} S :=
  fun a => (e a).rescale (r a : ℂ) (r a)

theorem forecastSiteFamilyRescale_eval
    (M N : A → ℕ) (hN : ∀ a, 0 < N a) (y : S → A → ℤ) :
    siteFamilyEval (forecastSiteFamilyRescale e (fun a => (N a : ℝ) / M a)) y
        (fun s a => (y s a : ℝ) / N a) =
      ((∏ a, (N a : ℝ) / M a : ℝ) : ℂ) *
        siteFamilyEval e y (fun s a => (y s a : ℝ) / M a) := by
  rw [siteFamilyEval_eq, siteFamilyEval_eq, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro a _
  exact (e a).rescale_integerEval (Complex.ofReal ((N a : ℝ) / M a)) (M a) (N a) (hN a)
    (fun s => y s a)

omit [Fintype A] in

theorem forecastSiteFamilyRescale_bounds
    {O W H : ℝ} (hW : 0 ≤ W) (hH : 0 ≤ H) (r : A → ℝ)
    (hr1 : ∀ a, 1 ≤ r a) (hrW : ∀ a, r a ≤ Real.exp W)
    (he : ∀ a, (e a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
      ⟨Real.exp O, Real.exp_nonneg _⟩ H) :
    ∀ a, (forecastSiteFamilyRescale e r a).Bounds
      (Real.exp (O + W)) (Real.exp (O + W)) (Real.exp (O + W))
      ⟨Real.exp (O + W), Real.exp_nonneg _⟩ H := by
  intro a
  have hr : 0 < r a := zero_lt_one.trans_le (hr1 a)
  have hnorm : ‖(r a : ℂ)‖ = r a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hnnnorm : (‖r a‖₊ : ℝ) = r a := by
    rw [coe_nnnorm, Real.norm_eq_abs, abs_of_pos hr]
  have hO : Real.exp O ≤ Real.exp (O + W) :=
    Real.exp_le_exp.mpr (le_add_of_nonneg_right hW)
  have hC : ‖(r a : ℂ)‖ * Real.exp O ≤ Real.exp (O + W) := by
    rw [hnorm, Real.exp_add]
    exact (mul_le_mul_of_nonneg_right (hrW a) (Real.exp_nonneg O)).trans_eq (mul_comm _ _)
  have hsupport : H / r a ≤ H := by
    apply (div_le_iff₀ hr).mpr
    exact le_mul_of_one_le_right hH (hr1 a)
  refine ((e a).rescale_bounds (he a) (r a : ℂ) hr).mono hO hO hC ?_ hsupport
  change Real.exp O * (‖r a‖₊ : ℝ) ≤ Real.exp (O + W)
  rw [hnnnorm, Real.exp_add]
  exact mul_le_mul_of_nonneg_left (hrW a) (Real.exp_nonneg O)

theorem forecastSiteFamilyRescale_ratio_bound
    (r : A → ℝ) {W : ℝ} (hr0 : ∀ a, 0 ≤ r a) (hrW : ∀ a, r a ≤ Real.exp W) :
    (∏ a, r a) ≤ Real.exp ((Fintype.card A : ℝ) * W) := by
  calc
    _ ≤ ∏ _a : A, Real.exp W :=
      Finset.prod_le_prod₀ (fun a _ => hr0 a) (fun a _ => hrW a)
    _ = (Real.exp W) ^ Fintype.card A := by simp
    _ = _ := (Real.exp_nat_mul W (Fintype.card A)).symm

theorem forecastSiteFamilyRescale_error
    (M N : A → ℕ) (hN : ∀ a, 0 < N a) (y : S → A → ℤ)
    (z : ℂ) (ε : ℝ)
    (he : ‖z - siteFamilyEval e y (fun s a => (y s a : ℝ) / M a)‖ ≤ ε) :
    ‖((∏ a, (N a : ℝ) / M a : ℝ) : ℂ) * z -
      siteFamilyEval (forecastSiteFamilyRescale e (fun a => (N a : ℝ) / M a)) y
        (fun s a => (y s a : ℝ) / N a)‖ ≤ (∏ a, (N a : ℝ) / M a) * ε := by
  rw [forecastSiteFamilyRescale_eval e M N hN y, ← mul_sub, norm_mul]
  have hr : 0 ≤ ∏ a, (N a : ℝ) / M a := Finset.prod_nonneg (fun _ _ => by positivity)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  exact mul_le_mul_of_nonneg_left he hr

theorem forecastSiteFamilyRescale_density_error
    (M N : A → ℕ) (hM : ∀ a, 0 < M a) (hN : ∀ a, 0 < N a)
    (y : S → A → ℤ) (z : ℂ) (ε : ℝ)
    (he : ‖((∏ a, (M a : ℝ) : ℝ) : ℂ) * z -
      siteFamilyEval e y (fun s a => (y s a : ℝ) / M a)‖ ≤ ε) :
    ‖((∏ a, (N a : ℝ) : ℝ) : ℂ) * z -
      siteFamilyEval (forecastSiteFamilyRescale e (fun a => (N a : ℝ) / M a)) y
        (fun s a => (y s a : ℝ) / N a)‖ ≤ (∏ a, (N a : ℝ) / M a) * ε := by
  have hratio : (∏ a, (N a : ℝ) / M a) * (∏ a, (M a : ℝ)) = ∏ a, (N a : ℝ) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro a _
    exact div_mul_cancel₀ _ (Nat.cast_pos.mpr (hM a)).ne'
  have htarget : ((∏ a, (N a : ℝ) / M a : ℝ) : ℂ) *
      (((∏ a, (M a : ℝ) : ℝ) : ℂ) * z) = ((∏ a, (N a : ℝ) : ℝ) : ℂ) * z := by
    rw [← mul_assoc, ← Complex.ofReal_mul, hratio]
  simpa only [htarget] using forecastSiteFamilyRescale_error e M N hN y
    (((∏ a, (M a : ℝ) : ℝ) : ℂ) * z) ε he

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ} (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (basis j) i
local notation "scale" => allocatedPrincipalGridScale (G := G) B U basis (R := R) j i
local notation "slots" => Finset.card (layerIntegerPrincipalSlots (G := G) B j i)
local notation "gamma" => principalProfileSize (R j) slots
local notation "ratio" => allocatedPrincipalChartRatio (G := G) B U basis (R := R) j i

theorem forecastInactiveScaleRatio_bounds (hR : 0 < R j) (hR1 : R j ≤ 1) :
    ratio ∈ Set.Icc 1 gamma⁻¹ := by
  have hheight : (0 : ℝ) < height := Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
  have hgamma : 0 < gamma := principalProfileSize_pos hR _
  have hgamma1 : gamma ≤ 1 := by
    unfold principalProfileSize
    apply (div_le_one (by positivity)).mpr
    have hs : (0 : ℝ) ≤ slots := Nat.cast_nonneg _
    linarith
  have hscale : (0 : ℝ) < scale := by
    apply Nat.cast_pos.mpr
    exact Nat.ceil_pos.mpr (mul_pos hgamma hheight)
  have hupper : scale ≤ height := by
    apply Nat.ceil_le.mpr
    exact mul_le_of_le_one_left hheight.le hgamma1
  have hlower : gamma * (height : ℝ) ≤ scale := Nat.le_ceil _
  constructor
  · change 1 ≤ (height : ℝ) / scale
    exact (one_le_div hscale).mpr (Nat.cast_le.mpr hupper)
  · change (height : ℝ) / scale ≤ gamma⁻¹
    rw [inv_eq_one_div]
    exact (div_le_div_iff₀ hscale hgamma).mpr (by simpa only [one_mul, mul_comm] using hlower)

theorem forecastInactiveProfile_inverse_exp {P : ℝ}
    (hR : 0 < R j) (hRinv : (R j)⁻¹ ≤ Real.exp P) (hslots : (slots : ℝ) ≤ P) :
    gamma⁻¹ ≤ Real.exp (4 * (P + 8)) := by
  have hP : 0 ≤ P := (Nat.cast_nonneg slots).trans hslots
  exact (allocatedProfile_inverse_exp_bounds slots hP hR (show (0 : ℝ) < 1 by norm_num)
    hRinv (by simpa only [inv_one] using Real.one_le_exp hP) hslots).2.1

theorem forecastInactiveScaleRatio_exp_bounds {P : ℝ}
    (hR : 0 < R j) (hR1 : R j ≤ 1)
    (hRinv : (R j)⁻¹ ≤ Real.exp P) (hslots : (slots : ℝ) ≤ P) :
    ratio ∈ Set.Icc 1 (Real.exp (4 * (P + 8))) := by
  obtain ⟨hl, hu⟩ := forecastInactiveScaleRatio_bounds B U basis j i hR hR1
  exact ⟨hl, hu.trans (forecastInactiveProfile_inverse_exp B j i hR hRinv hslots)⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem forecastIndependentScaleBudget
    {R : Fin m → ℝ} {pRadius Pearly Pblocks : ℝ}
    (hRadiusEarly : pRadius ≤ Pearly) (hEarly : 0 ≤ Pearly) (hBlocks : 0 ≤ Pblocks)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hblock : ∀ a : LayerSamplerAxis I n, (Fintype.card (B a) : ℝ) ≤ Pblocks) :
    0 ≤ Pearly + Pblocks ∧
      (∀ j, (R j)⁻¹ ≤ Real.exp (Pearly + Pblocks)) ∧
      (∀ j i, ((layerIntegerPrincipalSlots (G := G) B j i).card : ℝ) ≤ Pearly + Pblocks) := by
  refine ⟨add_nonneg hEarly hBlocks, ?_, ?_⟩
  · intro j
    exact (hRinv j).trans (Real.exp_le_exp.mpr (by linarith))
  · intro j i
    rw [layerIntegerPrincipalSlots_card]
    exact (hblock ⟨j, Sum.inr i⟩).trans (by linarith)

theorem forecastIndependentScaleBudget_of_total [∀ j, Fintype (I j)]
    {R : Fin m → ℝ} {pRadius Pearly Pblocks : ℝ}
    (hRadiusEarly : pRadius ≤ Pearly) (hEarly : 0 ≤ Pearly) (hBlocks : 0 ≤ Pblocks)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hblock : (∑ a : LayerSamplerAxis I n, (Fintype.card (B a) : ℝ)) ≤ Pblocks) :
    0 ≤ Pearly + Pblocks ∧
      (∀ j, (R j)⁻¹ ≤ Real.exp (Pearly + Pblocks)) ∧
      (∀ j i, ((layerIntegerPrincipalSlots (G := G) B j i).card : ℝ) ≤ Pearly + Pblocks) := by
  apply forecastIndependentScaleBudget (G := G) B hRadiusEarly hEarly hBlocks hRinv
  intro a
  exact (Finset.single_le_sum (f := fun x : LayerSamplerAxis I n => (Fintype.card (B x) : ℝ))
    (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ a)).trans hblock

theorem forecastIndependentScaleRatio_exp_bound
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R : Fin m → ℝ} {pRadius Pearly Pblocks : ℝ}
    (hR : ∀ j, 0 < R j) (hRone : ∀ j, R j ≤ 1)
    (hRadiusEarly : pRadius ≤ Pearly) (hEarly : 0 ≤ Pearly) (hBlocks : 0 ≤ Pblocks)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hblock : ∀ a : LayerSamplerAxis I n, (Fintype.card (B a) : ℝ) ≤ Pblocks)
    (j : Fin m) (i : Fin (n j)) :
    allocatedPrincipalChartRatio (G := G) B U basis (R := R) j i ∈
      Set.Icc 1 (Real.exp (4 * (Pearly + Pblocks + 8))) := by
  have h := forecastIndependentScaleBudget (G := G) B hRadiusEarly hEarly hBlocks hRinv hblock
  exact forecastInactiveScaleRatio_exp_bounds B U basis j i (hR j) (hRone j) (h.2.1 j) (h.2.2 j i)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

theorem forecastInactive_fixed_grid_mass_exp_bound
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    [∀ a, Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩)]
    {D P p Pscale : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D)
    (hP : 1 ≤ P) (hp : 0 ≤ p) (hPp : P ≤ Real.exp p)
    (hR1 : ∀ a, R (selected a).1 ≤ 1)
    (hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U b hR hσ S
      (selected a).1 (selected a).2 d).support)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hprimitive : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (hRinv : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp Pscale)
    (hslots : ∀ a, ((layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2).card : ℝ) ≤ Pscale)
    (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ) :
    let law := principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ)) *
      law.fiberMean (forecastInactiveFixedOutput B U b S selected c x)
        (fun a _ => z a) (fun _ => 1) ≤
      Real.exp (Fintype.card A * (allocatedInactivePointCapLog m D p 0 + 4 * (Pscale + 8))) := by
  intro law
  let r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod 1 := 0
  let cell : Finset (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
      (allocatedPrincipalSides B U b S)) := Finset.univ.filter (fun y => principalResidueLabel 1 y = r₀)
  have hcellEq : cell = Finset.univ := by
    ext y
    simp only [cell, Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_true_intro (Subsingleton.elim _ _)
  have hcellMass : law.mass cell = 1 := by
    rw [hcellEq]
    exact law.total
  have hcell : 0 < law.mass cell := by rw [hcellMass]; exact zero_lt_one
  let c₀ (a : A) := c a (constantCoefficientSlot _ _)
  let scale (a : A) := allocatedPrincipalGridScale (G := G) B U b (R := R)
    (selected a).1 (selected a).2
  let height (a : A) := basisAxisScale (b (selected a).1) (selected a).2
  let μ (a : A) := allocatedSupportedResidueJetPMF B U b hR hσ S 1 r₀ hcell
    (selected a).1 (selected a).2 (Finset.univ : Finset (Finset Empty)) (fun _ => c₀ a)
  let F := forecastInactiveFixedOutput B U b S selected c x
  have hjoint : (law.condition cell hcell).toPMF.map F = dependentProductPMF μ := by
    have h := forecastInactiveFixedPath_joint_law B U b hR hσ S 1 r₀ hcell
      selected hselected hsmall c hc x (fun _ => (Finset.univ : Finset (Finset Empty)))
    have hconst (c : ℤ) (t : Finset Empty) : booleanCoefficient (fun _ : Finset Empty => c) t = c := by
      simp only [booleanCoefficient_const, (Subsingleton.elim t ∅ : t = ∅), ↓reduceIte]
    unfold F forecastInactiveFixedOutput
    simpa only [hconst, law, cell, c₀, μ] using h
  have hmass : law.fiberMean F (fun a _ => z a) (fun _ => 1) =
      (dependentProductPMF μ (fun a _ => z a)).toReal := by
    rw [← hjoint, FiniteProbabilityWeights.toPMF_map_toReal,
      FiniteProbabilityWeights.condition_mean, hcellMass, hcellEq]
    simp only [Finset.mem_univ, ite_true, div_one]
    rfl
  let C := allocatedInactivePointCapLog m D p 0
  let W := 4 * (Pscale + 8)
  have hscale (a : A) : 0 < scale a :=
    allocatedPrincipalGridScale_pos_of_radius B U b hR (selected a).1 (selected a).2
  have hnormalized (a : A) : (scale a : ℝ) * (μ a (fun _ => z a)).toReal ≤ Real.exp C := by
    have h := forecastInactive_fixed_zero_axis_norm_le B U b S hR hσ
      (selected a).1 (selected a).2 1 zero_lt_one r₀ hD hP hp (le_refl 0) hPp
      (by simp) S.positive (hR1 a) (hsmall a) hcell L hL hprimitive (hB a) (c₀ a) (z a)
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg)] using h
  have hphysical (a : A) : (height a : ℝ) * (μ a (fun _ => z a)).toReal ≤
      Real.exp (C + W) := by
    have hr := forecastInactiveScaleRatio_exp_bounds B U b (selected a).1 (selected a).2
      (hR _) (hR1 a) (hRinv a) (hslots a)
    have hratio : (height a : ℝ) / scale a ≤ Real.exp W := hr.2
    calc
      (height a : ℝ) * (μ a (fun _ => z a)).toReal =
          ((height a : ℝ) / scale a) * ((scale a : ℝ) * (μ a (fun _ => z a)).toReal) := by
        rw [← mul_assoc, div_mul_cancel₀ _ (Nat.cast_pos.mpr (hscale a)).ne']
      _ ≤ Real.exp W * Real.exp C := mul_le_mul hratio (hnormalized a)
        (mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg) (Real.exp_nonneg _)
      _ = Real.exp (C + W) := by rw [← Real.exp_add, add_comm W C]
  change (∏ a, (height a : ℝ)) * law.fiberMean F (fun a _ => z a) (fun _ => 1) ≤ _
  rw [hmass, dependentProductPMF_apply, ENNReal.toReal_prod, ← Finset.prod_mul_distrib]
  calc
    (∏ a, (height a : ℝ) * (μ a (fun _ => z a)).toReal) ≤ ∏ _a : A, Real.exp (C + W) :=
      Finset.prod_le_prod₀ (fun _ _ => mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg)
        (fun a _ => hphysical a)
    _ = Real.exp (Fintype.card A * (C + W)) := by
      rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]

theorem forecastInactive_fixed_grid_fiber_exp_bound
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    [∀ a, Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩)]
    {D P p Pscale : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D)
    (hP : 1 ≤ P) (hp : 0 ≤ p) (hPp : P ≤ Real.exp p)
    (hR1 : ∀ a, R (selected a).1 ≤ 1)
    (hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U b hR hσ S
      (selected a).1 (selected a).2 d).support)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hprimitive : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (hRinv : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp Pscale)
    (hslots : ∀ a, ((layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2).card : ℝ) ≤ Pscale)
    (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) :
    let law := principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ)) *
      law.fiberMean (forecastInactiveFixedOutput B U b S selected c x)
        z (fun _ => 1) ≤
      Real.exp (Fintype.card A * (allocatedInactivePointCapLog m D p 0 + 4 * (Pscale + 8))) := by
  let t₀ : ((Finset.univ : Finset (Finset Empty)) : Type) := ⟨∅, Finset.mem_univ _⟩
  have hz : (fun a _ => z a t₀) = z := by
    funext a t
    exact congrArg (z a) (Subsingleton.elim _ _)
  have h := forecastInactive_fixed_grid_mass_exp_bound B U b S hR hσ selected hselected
    hD hP hp hPp hR1 hsmall c hc L hL hprimitive hB hRinv hslots x (fun a => z a t₀)
  simpa only [hz] using h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

attribute [local instance] ScalarSiteExpansion.termFinite

theorem exists_forecastInactive_fixed_physical_site
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    [∀ a, Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩)]
    (q : ℕ) [NeZero q]
    (coefficient : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q) → ℂ)
    (hcoefficient : ∀ r, ‖coefficient r‖ ≤ 1)
    {D P p v δ E : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D)
    (hP : 1 ≤ P) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hPp : P ≤ Real.exp p) (hqv : (q : ℝ) ≤ Real.exp v)
    (hδ : 0 < δ) (hE : 0 ≤ E)
    (hδE : δ⁻¹ ≤ Real.exp E)
    (hsize : q ≤ S.value) (hR1 : ∀ a, R (selected a).1 ≤ 1)
    (hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U b S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U b hR hσ S
      (selected a).1 (selected a).2 d).support)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hprimitive : scalarCubePrimitiveEnvelope Empty L 1 0 q ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    {Pscale : ℝ} (hPscale : 0 ≤ Pscale)
    (hRinv : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp Pscale)
    (hslots : ∀ a, ((layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2).card : ℝ) ≤ Pscale) :
    let law := principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let Pos := {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q //
      0 < law.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))}
    let scale := fun a => basisAxisScale (b (selected a).1) (selected a).2
    let W := 4 * (Pscale + 8)
    let O := allocatedInactiveJointSiteLog m D p v (E + D * W) + W
    ∃ e : Pos → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ r a, (e r a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (allocatedInactiveSupportLog D))) ∧
      (∑ t : Σ r, ∀ a, (e r a).Term, ‖forecastSiteMixtureCoefficient e
        (fun r => (law.mass (Finset.univ.filter
          (fun y => principalResidueLabel q y = r.val)) : ℂ) * coefficient r.val) t‖)
        ≤ Real.exp (Fintype.card A * O) ∧
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ),
        ‖((∏ a, (scale a : ℝ)) : ℂ) *
          law.complexMean (fun y => coefficient (principalResidueLabel q y) *
            (if forecastInactiveFixedOutput B U b S selected c x y = (fun a _ => z a)
              then (1 : ℂ) else 0)) -
          (∑ r : Pos, (law.mass (Finset.univ.filter
            (fun y => principalResidueLabel q y = r.val)) : ℂ) * coefficient r.val *
            siteFamilyEval (e r) (fun _ => z) (fun _ a => (z a : ℝ) / scale a))‖ ≤ δ := by
  intro law Pos height W O
  let scale := fun a => allocatedPrincipalGridScale (G := G) B U b (R := R)
    (selected a).1 (selected a).2
  let rate := fun a => (height a : ℝ) / scale a
  let rho := ∏ a, rate a
  let En := E + D * W
  let δn := δ * Real.exp (-(D * W))
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hEn : 0 ≤ En := add_nonneg hE (mul_nonneg hD.nonneg hW)
  have hδn : 0 < δn := mul_pos hδ (Real.exp_pos _)
  have hexpinv : (Real.exp (-(D * W)))⁻¹ = Real.exp (D * W) := by
    rw [← Real.exp_neg, neg_neg]
  have hδnE : δn⁻¹ ≤ Real.exp En := by
    calc
      δn⁻¹ = δ⁻¹ * Real.exp (D * W) := by
        dsimp only [δn]
        rw [mul_inv, hexpinv]
      _ ≤ Real.exp E * Real.exp (D * W) :=
        mul_le_mul_of_nonneg_right hδE (Real.exp_nonneg _)
      _ = Real.exp En := (Real.exp_add E (D * W)).symm
  have hcount : (Fintype.card A : ℝ) ≤ D :=
    (Nat.cast_le.mpr (Fintype.card_le_of_injective selected hselected)).trans
      (allocatedIntegerAxes_card_le B (fun _ => (Finset.univ : Finset (Finset Empty))) hD)
  have hscale (a : A) : 0 < scale a :=
    allocatedPrincipalGridScale_pos_of_radius B U b hR (selected a).1 (selected a).2
  have hheight (a : A) : 0 < height a := basisAxisScale_pos _ _
  have hrate (a : A) : rate a ∈ Set.Icc 1 (Real.exp W) :=
    forecastInactiveScaleRatio_exp_bounds B U b (selected a).1 (selected a).2
      (hR _) (hR1 a) (hRinv a) (hslots a)
  have hrho : 0 ≤ rho := Finset.prod_nonneg (fun a _ => zero_le_one.trans (hrate a).1)
  have hrhoBound : rho ≤ Real.exp (D * W) :=
    (forecastSiteFamilyRescale_ratio_bound rate (fun a => zero_le_one.trans (hrate a).1)
      (fun a => (hrate a).2)).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcount hW))
  obtain ⟨e, he, _, herr⟩ := exists_forecastInactive_fixed_residue_site B U b S hR hσ
    selected hselected q coefficient hcoefficient hD hP hp hv hPp hqv
    hδn hEn hδnE hsize hR1 hsmall hgrid c hc hσ1 L hL hprimitive hB
  let f := fun r : Pos => forecastSiteFamilyRescale (e r) rate
  have hf : ∀ r a, (f r a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
      ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (allocatedInactiveSupportLog D)) := by
    intro r
    exact forecastSiteFamilyRescale_bounds (e r) hW (Real.exp_nonneg _) rate
      (fun a => (hrate a).1) (fun a => (hrate a).2) (he r)
  let w (r : Pos) := law.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r.val))
  have hw (r : Pos) : 0 ≤ w r := law.mass_nonneg _
  have hmass : (∑ r : Pos, w r) ≤ 1 :=
    (forecastInactive_positiveResidue_mass_sum law (principalResidueLabel q)).le
  refine ⟨f, hf, ?_, ?_⟩
  · have hm := forecastSiteMixture_weighted_mass f hf (fun _ => Real.exp_nonneg O)
      w (fun r => coefficient r.val) hw hmass (fun r => hcoefficient r.val)
    simpa only [Finset.prod_const, Finset.card_univ, Real.exp_nat_mul] using hm
  · intro x z
    have hsum : (∑ r : Pos, (w r : ℂ) * coefficient r.val *
        siteFamilyEval (f r) (fun _ => z) (fun _ a => (z a : ℝ) / height a)) =
        (rho : ℂ) * (∑ r : Pos, (w r : ℂ) * coefficient r.val *
          siteFamilyEval (e r) (fun _ => z) (fun _ a => (z a : ℝ) / scale a)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      have heval := forecastSiteFamilyRescale_eval (e r) scale height hheight (fun _ => z)
      change siteFamilyEval (f r) (fun _ => z) (fun _ a => (z a : ℝ) / height a) =
        (rho : ℂ) * siteFamilyEval (e r) (fun _ => z) (fun _ a => (z a : ℝ) / scale a) at heval
      rw [heval]
      ring
    have hvolume : rho * (∏ a, (scale a : ℝ)) = ∏ a, (height a : ℝ) := by
      dsimp only [rho]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro a _
      exact div_mul_cancel₀ _ (Nat.cast_pos.mpr (hscale a)).ne'
    have htarget : ((∏ a, (height a : ℝ)) : ℂ) =
        (rho : ℂ) * ((∏ a, (scale a : ℝ)) : ℂ) := by
      exact_mod_cast hvolume.symm
    change ‖((∏ a, (height a : ℝ)) : ℂ) * _ -
      (∑ r : Pos, (w r : ℂ) * coefficient r.val *
        siteFamilyEval (f r) (fun _ => z) (fun _ a => (z a : ℝ) / height a))‖ ≤ δ
    rw [hsum, htarget, mul_assoc, ← mul_sub, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrho]
    calc
      _ ≤ rho * δn := mul_le_mul_of_nonneg_left (herr x z) hrho
      _ ≤ Real.exp (D * W) * δn := mul_le_mul_of_nonneg_right hrhoBound hδn.le
      _ = δ := by
        dsimp only [δn]
        rw [mul_left_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

end Erdos3.VectorPolynomial

end

end OAI
