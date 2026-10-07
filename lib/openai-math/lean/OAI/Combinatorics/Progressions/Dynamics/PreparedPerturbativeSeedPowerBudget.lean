/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.FinsetInj
import OAI.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleFullSliceLipschitz
import OAI.Combinatorics.Progressions.Estimates.SlicedToleranceMonotonicity
import OAI.Combinatorics.Progressions.Lattices.AllocatedAffineScaleEnvelope

namespace OAI

section

namespace Erdos3

theorem slicedPrincipalBoundaryRadius_inverse_le_exp (N : ℕ) {η P : ℝ}
    (hη : 0 < η) (hP : 0 ≤ P) (hN : (N : ℝ) + 1 ≤ Real.exp P)
    (hηP : η⁻¹ ≤ Real.exp P) :
    (slicedPrincipalBoundaryRadius N η)⁻¹ ≤ Real.exp (2 * P + 4) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h16 : (16 : ℝ) ≤ Real.exp 4 := by
    calc
      _ = (2 : ℝ) ^ 4 := by norm_num
      _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) h2 _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  unfold slicedPrincipalBoundaryRadius
  apply inv_min_le_of_inv_le
  · norm_num
    have he := Real.exp_le_exp.mpr (show 4 ≤ 2 * P + 4 by linarith)
    linarith [Real.add_one_le_exp (4 : ℝ)]
  · calc
      (η / (16 * ((N : ℝ) + 1)))⁻¹ = 16 * ((N : ℝ) + 1) * η⁻¹ := by rw [inv_div, div_eq_mul_inv]
      _ ≤ Real.exp 4 * Real.exp P * Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem slicedPrincipalMinor_inverse_le_exp (N m : ℕ) {a δ η P : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hη : 0 < η) (hP : 0 ≤ P)
    (hN : (N : ℝ) + 1 ≤ Real.exp P) (haP : a⁻¹ ≤ Real.exp P)
    (hδP : δ⁻¹ ≤ Real.exp P) (hηP : η⁻¹ ≤ Real.exp P) :
    (a * δ * (δ * slicedPrincipalBoundaryRadius N η) ^ m)⁻¹ ≤
      Real.exp (2 * P + (3 * P + 4) * m) := by
  have haInv : 0 < a⁻¹ := inv_pos.mpr ha
  have hr := (slicedPrincipalBoundaryRadius_spec N hη).1
  have hrP := slicedPrincipalBoundaryRadius_inverse_le_exp N hη hP hN hηP
  calc
    _ = (a⁻¹ * δ⁻¹) * (δ⁻¹ * (slicedPrincipalBoundaryRadius N η)⁻¹) ^ m := by
      simp only [mul_inv_rev]
      ring
    _ ≤ (Real.exp P * Real.exp P) * (Real.exp P * Real.exp (2 * P + 4)) ^ m := by gcongr
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

theorem slicedPrincipalComparisonBudget_le_exp (N m : ℕ) {C A r κ P : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hr : 0 < r) (hκ : 0 < κ) (hP : 0 ≤ P)
    (hN : (N : ℝ) ≤ Real.exp P) (hm : (m : ℝ) ≤ Real.exp P)
    (hCP : C ≤ Real.exp P) (hAP : A ≤ Real.exp P)
    (hrP : r⁻¹ ≤ Real.exp P) (hκP : κ⁻¹ ≤ Real.exp P) :
    slicedPrincipalComparisonBudget N m C A r κ ≤ Real.exp (8 * P + 5) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hH : (N : ℝ) * (N * ((m : ℝ) * ((m : ℝ) * C))) ≤ Real.exp (5 * P) := by
    calc
      _ ≤ Real.exp P * (Real.exp P * (Real.exp P * (Real.exp P * Real.exp P))) := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hH1 : (N : ℝ) * (N * ((m : ℝ) * ((m : ℝ) * C))) + 1 ≤ Real.exp (5 * P + 1) := by
    simpa only [add_comm] using one_add_le_exp_succ (by positivity : 0 ≤ 5 * P) hH
  have hS : 2 * κ⁻¹ * (2 * (N : ℝ) ^ 2 * A / r) ≤ Real.exp (5 * P + 2) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp 1 * Real.exp P * (Real.exp 1 * (Real.exp P)^2 * Real.exp P * Real.exp P) := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul]; simp only [← Real.exp_add]; congr 1; ring
  have hT : (N : ℝ) * ((2 * κ⁻¹)^2 * (N * (N * ((m : ℝ) * ((m : ℝ) * C))) + 1)) ≤
      Real.exp (8 * P + 3) := by
    calc
      _ ≤ Real.exp P * ((Real.exp 1 * Real.exp P)^2 * Real.exp (5 * P + 1)) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_nat_mul]; simp only [← Real.exp_add]; congr 1; ring
  have hS' := hS.trans (Real.exp_le_exp.mpr (show 5 * P + 2 ≤ 8 * P + 3 by linarith))
  have hsum : 2 * κ⁻¹ * (2 * (N : ℝ)^2 * A / r) +
      N * ((2 * κ⁻¹)^2 * (N * (N * ((m : ℝ) * ((m : ℝ) * C))) + 1)) ≤ Real.exp (8 * P + 4) := by
    calc
      _ ≤ 2 * Real.exp (8 * P + 3) := by linarith
      _ ≤ Real.exp 1 * Real.exp (8 * P + 3) := mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hb := one_add_le_exp_succ (by positivity : 0 ≤ 8 * P + 4) hsum
  rw [show 8 * P + 4 + 1 = 8 * P + 5 by ring] at hb
  simpa only [slicedPrincipalComparisonBudget, ← add_assoc] using hb

end Erdos3

end

section

namespace Erdos3

noncomputable def slicedPrincipalComparisonBudgetLog (D : ℝ) (m : ℕ)
    (P Rlog Klog : ℝ) : ℝ :=
  8 * (D + (m : ℝ) + P + Rlog + Klog + 8)

theorem slicedPrincipalComparisonBudget_le_exp_of_separate_logs (N m : ℕ)
    {D A r κ P Rlog Klog : ℝ}
    (hD : 0 ≤ D) (hN : (N : ℝ) ≤ D) (hA : 0 ≤ A)
    (hr : 0 < r) (hκ : 0 < κ)
    (hP : 0 ≤ P) (hRlog : 0 ≤ Rlog) (hKlog : 0 ≤ Klog)
    (hAP : A ≤ Real.exp P) (hrR : r⁻¹ ≤ Real.exp Rlog)
    (hκK : κ⁻¹ ≤ Real.exp Klog) :
    slicedPrincipalComparisonBudget N m 1 A r κ ≤
      Real.exp (slicedPrincipalComparisonBudgetLog D m P Rlog Klog) := by
  let H := D + (m : ℝ) + P + Rlog + Klog
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hDH : D ≤ H := by dsimp [H]; linarith
  have hmH : (m : ℝ) ≤ H := by dsimp [H]; linarith
  have hPH : P ≤ H := by dsimp [H]; linarith
  have hRH : Rlog ≤ H := by dsimp [H]; linarith
  have hKH : Klog ≤ H := by dsimp [H]; linarith
  have hNexp : (N : ℝ) ≤ Real.exp H :=
    hN.trans (hDH.trans (by linarith [Real.add_one_le_exp H]))
  have hmexp : (m : ℝ) ≤ Real.exp H :=
    hmH.trans (by linarith [Real.add_one_le_exp H])
  have h := slicedPrincipalComparisonBudget_le_exp N m zero_le_one hA hr hκ hH
    hNexp hmexp (Real.one_le_exp hH) (hAP.trans (Real.exp_le_exp.mpr hPH))
    (hrR.trans (Real.exp_le_exp.mpr hRH)) (hκK.trans (Real.exp_le_exp.mpr hKH))
  apply h.trans (Real.exp_le_exp.mpr ?_)
  dsimp [H, slicedPrincipalComparisonBudgetLog]
  linarith

end Erdos3

end

section

namespace Erdos3

theorem slicedEndpointUniformScale_inverse_le_exp (N O m : ℕ)
    {a δ A η P : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hA : 0 ≤ A) (hη : 0 < η) (hP : 0 ≤ P)
    (hN : (N : ℝ) + 1 ≤ Real.exp P) (hO : (O : ℝ) ≤ Real.exp P) (hm : (m : ℝ) ≤ Real.exp P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    (hAP : A ≤ Real.exp P) (hηP : η⁻¹ ≤ Real.exp P) :
    let L := (3 * P + 4) * m + 5 * P + 10
    (slicedPolynomialScale N O N m m 1 1 a δ A η)⁻¹ ≤ Real.exp (48 * L + 2 * P + 2 * m + 47) := by
  let L := (3 * P + 4) * m + 5 * P + 10
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hPL : P ≤ L := by dsimp [L]; nlinarith
  have hLP : Real.exp P ≤ Real.exp L := Real.exp_le_exp.mpr hPL
  let r := slicedPrincipalBoundaryRadius N η
  let κ := a * δ * (δ * r)^m
  have hr : 0 < r := (slicedPrincipalBoundaryRadius_spec N hη).1
  have hκ : 0 < κ := mul_pos (mul_pos ha hδ) (pow_pos (mul_pos hδ hr) _)
  have hN0 : (N : ℝ) ≤ Real.exp P := by linarith
  have hrL : r⁻¹ ≤ Real.exp L :=
    (slicedPrincipalBoundaryRadius_inverse_le_exp N hη hP hN hηP).trans
      (Real.exp_le_exp.mpr (by dsimp [L]; nlinarith))
  have hκL : κ⁻¹ ≤ Real.exp L :=
    (slicedPrincipalMinor_inverse_le_exp N m ha hδ hη hP hN haP hδP hηP).trans
      (Real.exp_le_exp.mpr (by dsimp [L]; nlinarith))
  let Q := slicedPrincipalComparisonBudget N m 1 A r κ
  have hQ : 0 ≤ Q := slicedPrincipalComparisonBudget_nonneg N m zero_le_one hA hr hκ
  have hQL : Q ≤ Real.exp (8 * L + 5) := slicedPrincipalComparisonBudget_le_exp N m
    zero_le_one hA hr hκ hL (hN0.trans hLP) (hm.trans hLP)
    (Real.one_le_exp_iff.mpr hL) (hAP.trans hLP) hrL hκL
  have hLS : L ≤ 8 * L + 6 := by linarith
  have hPS : P ≤ 8 * L + 6 := hPL.trans hLS
  have hhalf : (η / 2)⁻¹ ≤ Real.exp (8 * L + 6) := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ = 2 * η⁻¹ := by rw [inv_div, div_eq_mul_inv]
      _ ≤ Real.exp 1 * Real.exp P := by gcongr
      _ = Real.exp (P + 1) := by rw [← Real.exp_add, add_comm]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have ht : (slicedPrincipalC2Tolerance N O m 1 a δ A η)⁻¹ ≤ Real.exp (48 * L + 44) := by
    have he := polynomialPerturbationScale_inverse_le_exp (inv_nonneg.mpr hκ.le) zero_le_one hQ
      (half_pos hη) (show 0 ≤ 8 * L + 6 by positivity) O
      (hO.trans (Real.exp_le_exp.mpr hPS))
      (hκL.trans (Real.exp_le_exp.mpr hLS))
      (Real.one_le_exp_iff.mpr (by positivity))
      (hQL.trans (Real.exp_le_exp.mpr (by linarith))) hhalf
    change (slicedPrincipalC2Tolerance N O m 1 a δ A η)⁻¹ ≤ Real.exp (6 * (8 * L + 6) + 8) at he
    convert he using 1
    congr 1
    ring
  have hM : polynomialMassC2Budget N m 1 ≤ Real.exp (2 * P + 2 * m + 2) := by
    simpa only [add_zero] using polynomialMassC2Budget_le_exp N m hP zero_le_one hN0
      (show (1 : ℝ) ≤ Real.exp 0 by simp)
  have hM1 := one_add_le_exp_succ (show 0 ≤ 2 * P + 2 * m + 2 by positivity) hM
  have htpos := (slicedPrincipalC2Tolerance_pos_le_one N O m zero_le_one ha hδ hA hη).1
  change (slicedPolynomialScale N O N m m 1 1 a δ A η)⁻¹ ≤ _
  rw [slicedPolynomialScale, inv_div, div_eq_mul_inv]
  calc
    _ ≤ Real.exp (2 * P + 2 * m + 2 + 1) * Real.exp (48 * L + 44) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem slicedEndpointUniformScale_log_inverse_le (N O m : ℕ)
    {a δ A η P : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hA : 0 ≤ A) (hη : 0 < η) (hP : 0 ≤ P)
    (hN : (N : ℝ) + 1 ≤ Real.exp P) (hO : (O : ℝ) ≤ Real.exp P) (hm : (m : ℝ) ≤ Real.exp P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    (hAP : A ≤ Real.exp P) (hηP : η⁻¹ ≤ Real.exp P) :
    Real.log (slicedPolynomialScale N O N m m 1 1 a δ A η)⁻¹ ≤
      48 * ((3 * P + 4) * m + 5 * P + 10) + 2 * P + 2 * m + 47 := by
  have ht := (slicedEndpointUniformScale_spec N O m ha hδ hA hη).1
  exact (Real.log_le_log (inv_pos.mpr ht)
    (slicedEndpointUniformScale_inverse_le_exp N O m ha hδ hA hη hP hN hO hm haP hδP hAP hηP)).trans_eq
    (Real.log_exp _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D : Type*} [Fintype D] (B : D → Type*) [∀ d, Fintype (B d)]

theorem unitProfilePrincipalLowerBound_inv_le_exp {C : ℝ}
    (hsize : ((∑ d, Fintype.card (B d) : ℕ) : ℝ) ≤ C) :
    (unitProfilePrincipalLowerBound B)⁻¹ ≤ Real.exp (C + 4) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h8 : (8 : ℝ) ≤ Real.exp 3 := by
    calc
      _ = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (Real.exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) h2 _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hcard : ((∑ d, Fintype.card (B d) : ℕ) : ℝ) + 1 ≤ Real.exp C := by
    linarith [Real.add_one_le_exp C]
  simp only [unitProfilePrincipalLowerBound, one_div, inv_inv]
  calc
    _ ≤ Real.exp 3 * Real.exp C :=
      mul_le_mul h8 hcard (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (C + 3) := by rw [← Real.exp_add, add_comm]
    _ ≤ Real.exp (C + 4) := Real.exp_le_exp.mpr (by linarith)

theorem principalBlock_card_le_input_card (F : D → Type*) [∀ d, Fintype (F d)]
    (hF : ∀ d, 1 ≤ Fintype.card (F d)) :
    (∑ d, Fintype.card (B d)) ≤ Fintype.card (Σ d, B d × F d) := by
  rw [Fintype.card_sigma]
  apply Finset.sum_le_sum
  intro d _
  rw [Fintype.card_prod]
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left (Fintype.card (B d)) (hF d)

theorem unitProfilePrincipalLowerBound_inv_le_exp_of_input_card
    (F : D → Type*) [∀ d, Fintype (F d)]
    (hF : ∀ d, 1 ≤ Fintype.card (F d)) {C : ℝ}
    (hsize : (Fintype.card (Σ d, B d × F d) : ℝ) ≤ C) :
    (unitProfilePrincipalLowerBound B)⁻¹ ≤ Real.exp (C + 4) := by
  apply unitProfilePrincipalLowerBound_inv_le_exp B
  apply le_trans _ hsize
  exact_mod_cast principalBlock_card_le_input_card B F hF

namespace VectorPolynomial

theorem allocatedUnitProfilePrincipalLowerBound_inv_le_exp
    {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] {C : ℝ}
    (hsize : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ C) :
    (unitProfilePrincipalLowerBound B)⁻¹ ≤ Real.exp (C + 4) := by
  exact unitProfilePrincipalLowerBound_inv_le_exp_of_input_card B
    (fun a => Fin (layerSamplerDegree I n a))
    (fun a => by
      rw [Fintype.card_fin]
      exact Nat.succ_le_succ (Nat.zero_le _)) hsize

end VectorPolynomial

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : {a : LayerSamplerAxis I n // ¬short a},
  B (Subtype.val a) × Fin (degree (Subtype.val a)))

theorem allocatedOriginalSampleLiftLip_eq_card :
    allocatedOriginalSampleLiftLip B U basis S = (Fintype.card Input : ℝ≥0) * m := rfl

theorem allocatedOriginalSampleLiftLip_coe_eq_card :
    (allocatedOriginalSampleLiftLip B U basis S : ℝ) =
      (Fintype.card Input : ℝ) * (m : ℝ) := by
  simp only [allocatedOriginalSampleLiftLip, NNReal.coe_mul, NNReal.coe_natCast]

theorem allocatedOriginalSampleFullSliceLip_le_two {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    allocatedOriginalSampleFullSliceLip B U basis S t ≤
      2 * allocatedOriginalSampleLiftLip B U basis S := by
  unfold allocatedOriginalSampleFullSliceLip
  apply mul_le_mul_of_nonneg_right _ zero_le
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_add, NNReal.coe_one, NNReal.coe_ofNat,
    abs_of_nonneg ht0, Real.coe_toNNReal t ht0]
  linarith

theorem allocatedOriginalSampleFullSliceLip_coe_le_two {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (allocatedOriginalSampleFullSliceLip B U basis S t : ℝ) ≤
      2 * (allocatedOriginalSampleLiftLip B U basis S : ℝ) := by
  exact_mod_cast allocatedOriginalSampleFullSliceLip_le_two B U basis S ht0 ht1

theorem allocatedOriginalSampleLiftInput_card_le_allAxis :
    Fintype.card Input ≤ Fintype.card (PrincipalTupleIndex B degree) := by
  simp only [PrincipalTupleIndex, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  apply Finset.sum_le_sum_of_injOn Subtype.val
    (fun _ _ _ _ h => Subtype.val_injective h) (Finset.subset_univ _)
  · intro a _
    exact le_rfl
  · intro a _ _
    exact Nat.zero_le _

theorem allocatedOriginalSampleLiftLip_le_fullInputCount :
    allocatedOriginalSampleLiftLip B U basis S ≤
      (Fintype.card (PrincipalTupleIndex B degree) : ℝ≥0) * m := by
  rw [allocatedOriginalSampleLiftLip_eq_card]
  apply mul_le_mul_of_nonneg_right _ zero_le
  exact_mod_cast allocatedOriginalSampleLiftInput_card_le_allAxis B U basis S

theorem allocatedOriginalSampleLiftLip_coe_le_allAxis :
    (allocatedOriginalSampleLiftLip B U basis S : ℝ) ≤
      (Fintype.card (PrincipalTupleIndex B degree) : ℝ) * (m : ℝ) := by
  exact_mod_cast allocatedOriginalSampleLiftLip_le_fullInputCount B U basis S

theorem allocatedOriginalSampleLiftLip_le_exp_of_allAxis {P : ℝ}
    (hcount : (Fintype.card (PrincipalTupleIndex B degree) : ℝ) * (m : ℝ) ≤ P) :
    (allocatedOriginalSampleLiftLip B U basis S : ℝ) ≤ Real.exp P := by
  exact (allocatedOriginalSampleLiftLip_coe_le_allAxis B U basis S).trans
    (hcount.trans (by linarith [Real.add_one_le_exp P]))

theorem allocatedOriginalSampleFullSliceLip_le_two_exp_of_allAxis
    {P t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hcount : (Fintype.card (PrincipalTupleIndex B degree) : ℝ) * (m : ℝ) ≤ P) :
    (allocatedOriginalSampleFullSliceLip B U basis S t : ℝ) ≤ 2 * Real.exp P :=
  (allocatedOriginalSampleFullSliceLip_coe_le_two B U basis S ht0 ht1).trans
    (mul_le_mul_of_nonneg_left
      (allocatedOriginalSampleLiftLip_le_exp_of_allAxis B U basis S hcount) (by norm_num))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def fixedPathPerturbationLog (D P E : ℝ) (m : ℕ) : ℝ :=
  let Q := D + P + E + m + 2
  48 * ((3 * Q + 4) * m + 5 * Q + 10) + 2 * Q + 2 * m + 47

theorem fixedPathPerturbationLog_nonneg {D P E : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E) (m : ℕ) :
    0 ≤ fixedPathPerturbationLog D P E m := by
  unfold fixedPathPerturbationLog
  positivity

theorem fixedPathPerturbation_scale_lower
    (N O m : ℕ) {D P E a A η : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hN : (N : ℝ) ≤ D) (hO : (O : ℝ) ≤ D)
    (ha : 0 < a) (hA : 0 ≤ A) (hη : 0 < η)
    (haP : a⁻¹ ≤ Real.exp P) (hAP : A ≤ Real.exp P) (hηE : η⁻¹ ≤ Real.exp E) :
    Real.exp (-fixedPathPerturbationLog D P E m) ≤
      slicedPolynomialScale N O N m m 1 1 a (1 / 2) A η := by
  let Q := D + P + E + m + 2
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hDQ : D ≤ Q := by dsimp only [Q]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hPQ : P ≤ Q := by dsimp only [Q]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hEQ : E ≤ Q := by dsimp only [Q]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hmQ : (m : ℝ) ≤ Q := by dsimp only [Q]; linarith
  have hNQ : (N : ℝ) + 1 ≤ Real.exp Q :=
    ((show (N : ℝ) + 1 ≤ D + 1 by linarith).trans
      (Real.add_one_le_exp D)).trans (Real.exp_le_exp.mpr hDQ)
  have hOQ : (O : ℝ) ≤ Real.exp Q :=
    hO.trans ((by linarith [Real.add_one_le_exp D] : D ≤ Real.exp D).trans
      (Real.exp_le_exp.mpr hDQ))
  have hmexp : (m : ℝ) ≤ Real.exp Q :=
    (by linarith [Real.add_one_le_exp (m : ℝ)] : (m : ℝ) ≤ Real.exp m).trans
      (Real.exp_le_exp.mpr hmQ)
  have hδQ : (1 / 2 : ℝ)⁻¹ ≤ Real.exp Q := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    norm_num only [one_div, inv_inv]
    exact htwo.trans (Real.exp_le_exp.mpr (by dsimp only [Q]; linarith [Nat.cast_nonneg (α := ℝ) m]))
  have hi := slicedEndpointUniformScale_inverse_le_exp N O m ha (by norm_num) hA hη hQ
    hNQ hOQ hmexp (haP.trans (Real.exp_le_exp.mpr hPQ)) hδQ
    (hAP.trans (Real.exp_le_exp.mpr hPQ)) (hηE.trans (Real.exp_le_exp.mpr hEQ))
  have hs := (slicedEndpointUniformScale_spec N O m ha (by norm_num : (0 : ℝ) < 1 / 2) hA hη).1
  rw [Real.exp_neg]
  exact inv_le_of_inv_le₀ hs (by simpa only [fixedPathPerturbationLog, Q] using hi)

theorem fixedPathPerturbation_tail
    (N O m : ℕ) {D P E a A η : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hN : (N : ℝ) ≤ D) (hO : (O : ℝ) ≤ D)
    (ha : 0 < a) (hA : 0 ≤ A) (hη : 0 < η)
    (haP : a⁻¹ ≤ Real.exp P) (hAP : A ≤ Real.exp P) (hηE : η⁻¹ ≤ Real.exp E)
    {N' O' : ℕ} (hNN : N' ≤ N) (hOO : O' ≤ O) {t : ℝ}
    (ht : |t| ≤ Real.exp (-fixedPathPerturbationLog D P E m)) :
    |t| * polynomialMassC2Budget N' m 1 ≤
      slicedPrincipalC2Tolerance N' O' m 1 a (1 / 2) A η :=
  (slicedEndpointUniformScale_spec N O m ha (by norm_num) hA hη).2.2 N' O' hNN hOO t
    (ht.trans (fixedPathPerturbation_scale_lower N O m hD hP hE hN hO ha hA hη haP hAP hηE))

theorem fixedPathPerturbation_tolerance_ratio_lower
    (N O m : ℕ) {D P E a A η : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hN : (N : ℝ) ≤ D) (hO : (O : ℝ) ≤ D)
    (ha : 0 < a) (hA : 0 ≤ A) (hη : 0 < η)
    (haP : a⁻¹ ≤ Real.exp P) (hAP : A ≤ Real.exp P) (hηE : η⁻¹ ≤ Real.exp E)
    {N' O' : ℕ} (hNN : N' ≤ N) (hOO : O' ≤ O) :
    Real.exp (-fixedPathPerturbationLog D P E m) ≤
      slicedPrincipalC2Tolerance N' O' m 1 a (1 / 2) A η /
        polynomialMassC2Budget N' m 1 := by
  apply (le_div_iff₀ (by unfold polynomialMassC2Budget; positivity)).mpr
  simpa only [abs_of_pos (Real.exp_pos _)] using
    fixedPathPerturbation_tail N O m hD hP hE hN hO ha hA hη haP hAP hηE hNN hOO
      (t := Real.exp (-fixedPathPerturbationLog D P E m)) (by rw [abs_of_pos (Real.exp_pos _)])

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}

theorem allocatedFixedPathPerturbation_tail_uniform
    {D P E η : ℝ} (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hInput : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ D)
    (hAxis : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D)
    (A : ℝ≥0) (hη : 0 < η)
    (haP : (unitProfilePrincipalLowerBound B)⁻¹ ≤ Real.exp P)
    (hAP : (A : ℝ) ≤ Real.exp P) (hηE : η⁻¹ ≤ Real.exp E)
    {t : ℝ} (ht : |t| ≤ Real.exp (-fixedPathPerturbationLog D P E m))
    (S : LayerSamplerScale (G := G) B U basis R σ) :
    let active := fun a => ¬allocatedShortAxis (I := I) U basis S.value a
    let inputs := PrincipalTupleIndex (fun a : {a // active a} => B a.val)
      (fun a => layerSamplerDegree I n a.val)
    |t| * polynomialMassC2Budget (Fintype.card inputs) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card inputs) (Fintype.card {a // active a})
        m 1 (unitProfilePrincipalLowerBound B) (1 / 2) A η := by
  intro active inputs
  exact fixedPathPerturbation_tail
    (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)))
    (Fintype.card (LayerSamplerAxis I n)) m hD hP hE hInput hAxis
    (unitProfilePrincipalLowerBound_pos B) A.coe_nonneg hη haP hAP hηE
    (allocatedOriginalSampleLiftInput_card_le_allAxis B U basis S)
    (Fintype.card_subtype_le _) ht

theorem allocatedFixedPathPerturbation_ratio_lower_uniform
    {D P E η : ℝ} (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hInput : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ D)
    (hAxis : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D)
    (A : ℝ≥0) (hη : 0 < η)
    (haP : (unitProfilePrincipalLowerBound B)⁻¹ ≤ Real.exp P)
    (hAP : (A : ℝ) ≤ Real.exp P) (hηE : η⁻¹ ≤ Real.exp E)
    (S : LayerSamplerScale (G := G) B U basis R σ) :
    let active := fun a => ¬allocatedShortAxis (I := I) U basis S.value a
    let inputs := PrincipalTupleIndex (fun a : {a // active a} => B a.val)
      (fun a => layerSamplerDegree I n a.val)
    Real.exp (-fixedPathPerturbationLog D P E m) ≤
      slicedPrincipalC2Tolerance (Fintype.card inputs) (Fintype.card {a // active a})
        m 1 (unitProfilePrincipalLowerBound B) (1 / 2) A η /
          polynomialMassC2Budget (Fintype.card inputs) m 1 := by
  intro active inputs
  exact fixedPathPerturbation_tolerance_ratio_lower
    (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)))
    (Fintype.card (LayerSamplerAxis I n)) m hD hP hE hInput hAxis
    (unitProfilePrincipalLowerBound_pos B) A.coe_nonneg hη haP hAP hηE
    (allocatedOriginalSampleLiftInput_card_le_allAxis B U basis S)
    (Fintype.card_subtype_le _)

theorem allocatedFixedPathPerturbation_tail_of_inputCount
    {D P E η : ℝ} (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hInput : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ D)
    (hAxis : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D)
    (A : ℝ≥0) (hη : 0 < η) (hAP : (A : ℝ) ≤ Real.exp P) (hηE : η⁻¹ ≤ Real.exp E)
    {t : ℝ} (ht : |t| ≤ Real.exp (-fixedPathPerturbationLog D (D + P + 4) E m))
    (S : LayerSamplerScale (G := G) B U basis R σ) :
    let active := fun a => ¬allocatedShortAxis (I := I) U basis S.value a
    let inputs := PrincipalTupleIndex (fun a : {a // active a} => B a.val)
      (fun a => layerSamplerDegree I n a.val)
    |t| * polynomialMassC2Budget (Fintype.card inputs) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card inputs) (Fintype.card {a // active a})
        m 1 (unitProfilePrincipalLowerBound B) (1 / 2) A η := by
  exact allocatedFixedPathPerturbation_tail_uniform B U basis hD (by positivity) hE
    hInput hAxis A hη
    ((allocatedUnitProfilePrincipalLowerBound_inv_le_exp B hInput).trans
      (Real.exp_le_exp.mpr (by linarith)))
    (hAP.trans (Real.exp_le_exp.mpr (by linarith))) hηE ht S

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedPerturbativeSeed_power_budget (m inputPower : ℕ) :
    ∃ outputPower : ℕ, 2 ≤ outputPower ∧ ∀ {p : ℝ}, 0 ≤ p →
      ∀ D pRadius Ptail Prho Pk target F Tmod Ppert Epert : ℝ,
        D ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        pRadius ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        Ptail ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        Prho ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        Pk ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        target ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        F ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        Tmod ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        Ppert ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        Epert ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        let Qσ := fixedPathPerturbationLog D (D + Ppert + 4) Epert m
        let Pscale := pRadius + Ptail + Qσ
        let lengthLog := allocatedAffineLengthLog m D Pscale Prho Pk target F Tmod
        let Pseed := allocatedScaleLog (D + Pscale + lengthLog + 1)
        Qσ ∈ Set.Icc 0 ((p + 2) ^ outputPower) ∧
        Pscale ∈ Set.Icc 0 ((p + 2) ^ outputPower) ∧
        Pseed ∈ Set.Icc 0 ((p + 2) ^ outputPower) := by
  obtain ⟨A, _, hseed⟩ := exists_allocatedAffineScaleLog_bound m
  let T : Polynomial ℕ := (Polynomial.X + 2) ^ inputPower
  let B : Polynomial ℕ := 4 * T + Polynomial.C m + 6
  let sigma : Polynomial ℕ := 48 * ((3 * B + 4) * Polynomial.C m + 5 * B + 10) +
    2 * B + 2 * Polynomial.C m + 47
  let scale : Polynomial ℕ := 2 * T + sigma
  let bound : Polynomial ℕ := sigma + scale + (6 * T + scale + Polynomial.C A) ^ A
  obtain ⟨outputPower, houtputPower, hbound⟩ := exists_natPolynomial_fixed_power_budget bound
  refine ⟨outputPower, houtputPower, ?_⟩
  intro p hp D pRadius Ptail Prho Pk target F Tmod Ppert Epert
    hD hRadius hTail hRho hK hTarget hF hTmod hPert hEpert Qσ Pscale lengthLog Pseed
  let t := (p + 2) ^ inputPower
  let b := 4 * t + (m : ℝ) + 6
  let sigmaBound := 48 * ((3 * b + 4) * (m : ℝ) + 5 * b + 10) + 2 * b + 2 * m + 47
  let scaleBound := 2 * t + sigmaBound
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hSigmaBound : 0 ≤ sigmaBound := by dsimp [sigmaBound]; positivity
  have hScaleBound : 0 ≤ scaleBound := by dsimp [scaleBound]; positivity
  have hPert0 : 0 ≤ D + Ppert + 4 := by linarith [hD.1, hPert.1]
  have hσ : 0 ≤ Qσ := fixedPathPerturbationLog_nonneg hD.1 hPert0 hEpert.1 m
  have hσB : Qσ ≤ sigmaBound := by
    have hinner : D + (D + Ppert + 4) + Epert + (m : ℝ) + 2 ≤ b := by
      dsimp [b, t]
      linarith [hD.2, hPert.2, hEpert.2]
    dsimp only [Qσ, fixedPathPerturbationLog, sigmaBound]
    gcongr
  have hscale : 0 ≤ Pscale := add_nonneg (add_nonneg hRadius.1 hTail.1) hσ
  have hscaleB : Pscale ≤ scaleBound := by
    dsimp [Pscale, scaleBound, t]
    linarith [hRadius.2, hTail.2]
  have hLength : 0 ≤ lengthLog :=
    (allocatedAffineLengthLog_bounds m hD.1 hscale hRho.1 hK.1 hTarget.1 hF.1 hTmod.1).2.2.1
  have hSeed : 0 ≤ Pseed := allocatedScaleLog_nonneg (by linarith [hD.1])
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  have hSeedB : Pseed ≤ (6 * t + scaleBound + A) ^ A := by
    apply (hseed D Pscale Prho Pk target F Tmod hD.1 hscale hRho.1 hK.1
      hTarget.1 hF.1 hTmod.1).trans
    apply pow_le_pow_left₀ (by linarith [hD.1, hRho.1, hK.1, hTarget.1, hF.1, hTmod.1])
    dsimp [t]
    linarith [hD.2, hRho.2, hK.2, hTarget.2, hF.2, hTmod.2]
  have hmajor : sigmaBound + scaleBound + (6 * t + scaleBound + A) ^ A ≤
      (p + 2) ^ outputPower := by
    simpa [bound, scale, sigma, B, T, t, b, sigmaBound, scaleBound,
      Polynomial.eval₂_pow] using hbound p hp
  have hlast : 0 ≤ (6 * t + scaleBound + A) ^ A := by positivity
  refine ⟨⟨hσ, ?_⟩, ⟨hscale, ?_⟩, ⟨hSeed, ?_⟩⟩ <;> linarith

end Erdos3.VectorPolynomial

end

end OAI
