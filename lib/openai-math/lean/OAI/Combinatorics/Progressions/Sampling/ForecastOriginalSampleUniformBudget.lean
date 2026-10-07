/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Sampling.AllocatedOriginalSampleForecastAtom

namespace OAI

section

namespace Erdos3.VectorPolynomial

def forecastOriginalSmoothBudget (m : ℕ) (P : ℝ) : ℝ :=
  (10 * (m : ℝ) + 30) * (P + 1) ^ 2

theorem forecastOriginalSmoothBudget_bounds (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    let Q := ((m : ℝ) + 2) * P + 4 * m + 8
    0 ≤ forecastOriginalSmoothBudget m P ∧
      P * (2 * P + 1) + P * (Q + 1) + 1 ≤ forecastOriginalSmoothBudget m P ∧
      2 * P * (2 * P + 1) + 2 * P * (Q + 1) + 2 * P + (4 * P + 2) +
        2 * Q + 2 ≤ forecastOriginalSmoothBudget m P := by
  intro Q
  refine ⟨?_, ?_, ?_⟩
  · unfold forecastOriginalSmoothBudget
    positivity
  · apply sub_nonneg.mp
    have he : forecastOriginalSmoothBudget m P -
        (P * (2 * P + 1) + P * (Q + 1) + 1) =
        (9 * (m : ℝ) + 26) * P ^ 2 + (16 * m + 50) * P + (10 * m + 29) := by
      unfold forecastOriginalSmoothBudget Q
      ring
    rw [he]
    positivity
  · apply sub_nonneg.mp
    have he : forecastOriginalSmoothBudget m P -
        (2 * P * (2 * P + 1) + 2 * P * (Q + 1) + 2 * P + (4 * P + 2) + 2 * Q + 2) =
        (8 * (m : ℝ) + 22) * P ^ 2 + (10 * m + 30) * P + (2 * m + 10) := by
      unfold forecastOriginalSmoothBudget Q
      ring
    rw [he]
    positivity

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedForecastAllAxisRowCap_le_exp {P δ : ℝ}
    (hP : 1 ≤ P) (hblocks : (∑ a, (Fintype.card (B a) : ℝ)) ≤ P)
    (hδ : 0 < δ) (hδinv : δ⁻¹ ≤ Real.exp P) (a : LayerSamplerAxis I n) :
    (allocatedForecastAllAxisRowCap B hδ a : ℝ) ≤
      Real.exp (((m : ℝ) + 2) * P + 4 * m + 8) := by
  let q := Fintype.card {k : Fin (layerSamplerDegree I n a) //
    k ≠ ⟨0, Nat.zero_lt_succ _⟩}
  have hq : q ≤ m := calc
    _ ≤ Fintype.card (Fin (layerSamplerDegree I n a)) := Fintype.card_subtype_le _
    _ = a.1.val + 1 := Fintype.card_fin _
    _ ≤ m := Nat.succ_le_of_lt a.1.isLt
  have hqR : (q : ℝ) ≤ m := by exact_mod_cast hq
  have hp : 0 ≤ P := zero_le_one.trans hP
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hprincipal : (unitProfilePrincipalLowerBound B)⁻¹ ≤ Real.exp (P + 8) := by
    calc
      _ = 8 * ((∑ a, (Fintype.card (B a) : ℝ)) + 1) := by
        simp only [unitProfilePrincipalLowerBound, one_div, inv_inv, Nat.cast_sum]
      _ ≤ 8 * Real.exp P :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp P]) (by norm_num)
      _ ≤ Real.exp 8 * Real.exp P := mul_le_mul_of_nonneg_right h8 (Real.exp_nonneg _)
      _ = Real.exp (P + 8) := by rw [← Real.exp_add, add_comm]
  change (unitProfilePrincipalLowerBound B * δ ^ (q + 1))⁻¹ * 4 ^ q ≤ _
  rw [mul_inv_rev, ← inv_pow]
  calc
    _ ≤ ((Real.exp P) ^ (q + 1) * Real.exp (P + 8)) * (Real.exp 4) ^ q := by
      gcongr
      exact inv_nonneg.mpr (unitProfilePrincipalLowerBound_pos B).le
    _ = Real.exp (((q : ℝ) + 1) * P + (P + 8) + q * 4) := by
      simp only [← Real.exp_nat_mul, ← Real.exp_add, Nat.cast_add, Nat.cast_one]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hqR hp]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

theorem allocatedForecastAllAxisLift_budget
    {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {P δ : ℝ} (hP : 1 ≤ P) (hδ : 0 < δ) (hδinv : δ⁻¹ ≤ Real.exp P)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ P)
    (hblocks : (∑ a, (Fintype.card (B a) : ℝ)) ≤ P) :
    let Q := ((m : ℝ) + 2) * P + 4 * m + 8
    let E := P * (Q + 1)
    (allocatedForecastAllAxisLiftCap B hδ : ℝ) ≤ Real.exp E ∧
      (allocatedForecastAllAxisLiftLip B hδ : ℝ) ≤ Real.exp (E + P + 2 * Q + 1) := by
  intro Q E
  let A := allocatedForecastAllAxisRowCap B hδ
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hrow (a : LayerSamplerAxis I n) : (A a : ℝ) ≤ Real.exp Q :=
    allocatedForecastAllAxisRowCap_le_exp B hP hblocks hδ hδinv a
  have hA : (allocatedForecastAllAxisLiftCap B hδ : ℝ) ≤ Real.exp E := by
    change ((∏ a, (A a + 1 : ℝ≥0) : ℝ≥0) : ℝ) ≤ _
    rw [NNReal.coe_prod]
    calc
      _ ≤ ∏ _a : LayerSamplerAxis I n, Real.exp (Q + 1) := by
        apply Finset.prod_le_prod₀
        · intro a _
          positivity
        · intro a _
          simpa only [NNReal.coe_add, NNReal.coe_one, add_comm] using
            one_add_le_exp_succ hQ (hrow a)
      _ = (Real.exp (Q + 1)) ^ Fintype.card (LayerSamplerAxis I n) := by simp
      _ ≤ Real.exp E :=
        pow_le_exp_mul_of_le_exp (Real.exp_nonneg _) le_rfl (by positivity) _ haxes
  have hcount : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ Real.exp P :=
    haxes.trans (by linarith [Real.add_one_le_exp P])
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hsum : ((∑ a, A a * (2 * A a) : ℝ≥0) : ℝ) ≤ Real.exp (P + (2 * Q + 1)) := by
    rw [NNReal.coe_sum]
    calc
      _ ≤ ∑ _a : LayerSamplerAxis I n, Real.exp (2 * Q + 1) := by
        apply Finset.sum_le_sum
        intro a _
        push_cast
        calc
          _ ≤ Real.exp Q * (Real.exp 1 * Real.exp Q) := by
            gcongr
            exact hrow a
            exact hrow a
          _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ = (Fintype.card (LayerSamplerAxis I n) : ℝ) * Real.exp (2 * Q + 1) := by simp
      _ ≤ Real.exp P * Real.exp (2 * Q + 1) :=
        mul_le_mul_of_nonneg_right hcount (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  refine ⟨hA, ?_⟩
  rw [allocatedForecastAllAxisLiftLip, NNReal.coe_mul]
  calc
    _ ≤ Real.exp E * Real.exp (P + (2 * Q + 1)) :=
      mul_le_mul hA hsum (by positivity) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

private theorem forecastEmptySpatial_budget {Z : Type*} [Fintype Z]
    (s : Empty ↪ Z) {P : ℝ} (hP : 0 ≤ P) (hZ : (Fintype.card Z : ℝ) ≤ P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) :
    ((Real.toNNReal (anisotropicSpatialDensityCap s 1) + 1 : ℝ≥0) : ℝ) ≤ Real.exp (2 * P + 1) ∧
      (Real.toNNReal (anisotropicSpatialDensityLip s 1) : ℝ) ≤ Real.exp (4 * P + 2) := by
  have hfree : (Fintype.card (UnselectedColumn s) : ℝ) ≤ P := by
    have hc := selectedColumn_card s
    exact (Nat.cast_le.mpr (show Fintype.card (UnselectedColumn s) ≤ Fintype.card Z by omega)).trans hZ
  have hinv : physicalSpatialInverseBound Empty 1 = 1 := by
    norm_num [physicalSpatialInverseBound]
  have hcap : anisotropicSpatialDensityCap s 1 ≤ Real.exp (2 * P) := by
    have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    have hh := pow_le_exp_mul_of_le_exp (by norm_num : (0 : ℝ) ≤ 2) htwo
      (by norm_num : (0 : ℝ) ≤ 2) (Fintype.card (UnselectedColumn s)) hfree
    simpa [anisotropicSpatialDensityCap, hinv, mul_comm P 2] using hh
  have hcount : (Fintype.card (UnselectedColumn s) : ℝ) + 1 ≤ Real.exp (P + 1) := by
    calc
      _ ≤ P + 1 := by linarith
      _ ≤ Real.exp (P + 1) := by linarith [Real.add_one_le_exp (P + 1)]
  have hlip : anisotropicSpatialDensityLip s 1 ≤ Real.exp (4 * P + 2) := by
    simp only [anisotropicSpatialDensityLip, hinv, mul_one,
      Fintype.card_sum, Fintype.card_unit, Fintype.card_empty, Nat.add_zero, Nat.cast_one]
    calc
      _ ≤ Real.exp (2 * P) * (Real.exp (P + 1) * Real.exp P) := by
        gcongr
      _ = Real.exp (4 * P + 1) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  constructor
  · simpa only [NNReal.coe_add, NNReal.coe_one, add_comm] using
      one_add_le_exp_succ (by positivity : 0 ≤ 2 * P) (coe_toNNReal_le_exp hcap)
  · exact coe_toNNReal_le_exp hlip

def forecastOriginalSmoothCapLog (P Q : ℝ) : ℝ :=
  P * (2 * P + 1) + P * (Q + 1) + 1

def forecastOriginalSmoothLipLog (P Q : ℝ) : ℝ :=
  2 * P * (2 * P + 1) + 2 * P * (Q + 1) + 2 * P + (4 * P + 2) + 2 * Q + 2

private theorem forecastAllAxis_budget
    {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {X Z : Type*} [Fintype X] [Fintype Z] (s : Empty ↪ Z)
    {P Q δ : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hδ : 0 < δ)
    (hX : (Fintype.card X : ℝ) ≤ P) (hZ : (Fintype.card Z : ℝ) ≤ P)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hrow : ∀ a, (allocatedForecastAllAxisRowCap B hδ a : ℝ) ≤ Real.exp Q) :
    (allocatedForecastAllAxisCap (X := X) B hδ s : ℝ) + 1 ≤
        Real.exp (forecastOriginalSmoothCapLog P Q) ∧
      (allocatedForecastAllAxisLip (X := X) B hδ s : ℝ) ≤
        Real.exp (forecastOriginalSmoothLipLog P Q) := by
  let C := Real.toNNReal (anisotropicSpatialDensityCap s 1) + 1
  let K := Real.toNNReal (anisotropicSpatialDensityLip s 1)
  let A := allocatedForecastAllAxisRowCap B hδ
  let E := P * (Q + 1)
  let F := P * (2 * P + 1)
  have hs := forecastEmptySpatial_budget s hP hZ hprofile
  have hC : ((C ^ Fintype.card X : ℝ≥0) : ℝ) ≤ Real.exp F := by
    rw [NNReal.coe_pow]
    exact pow_le_exp_mul_of_le_exp C.coe_nonneg hs.1 (by positivity) _ hX
  have hK : (K : ℝ) ≤ Real.exp (4 * P + 2) := hs.2
  have hA : (allocatedForecastAllAxisLiftCap B hδ : ℝ) ≤ Real.exp E := by
    change ((∏ a, (A a + 1 : ℝ≥0) : ℝ≥0) : ℝ) ≤ _
    rw [NNReal.coe_prod]
    calc
      _ ≤ ∏ _a : LayerSamplerAxis I n, Real.exp (Q + 1) := by
        apply Finset.prod_le_prod₀
        · intro a _; positivity
        · intro a _
          simpa only [NNReal.coe_add, NNReal.coe_one, add_comm] using
            one_add_le_exp_succ hQ (hrow a)
      _ = (Real.exp (Q + 1)) ^ Fintype.card (LayerSamplerAxis I n) := by simp
      _ ≤ Real.exp E := pow_le_exp_mul_of_le_exp (Real.exp_nonneg _) le_rfl (by positivity) _ haxes
  have hcount (d : ℕ) (hd : (d : ℝ) ≤ P) : (d : ℝ) ≤ Real.exp P :=
    hd.trans (by linarith [Real.add_one_le_exp P])
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hsum : (∑ a, A a * (2 * A a) : ℝ≥0) ≤ Real.exp (P + (2 * Q + 1)) := by
    rw [NNReal.coe_sum]
    calc
      _ ≤ ∑ _a : LayerSamplerAxis I n, Real.exp (2 * Q + 1) := by
        apply Finset.sum_le_sum
        intro a _
        push_cast
        calc
          _ ≤ Real.exp Q * (Real.exp 1 * Real.exp Q) := by gcongr; exact hrow a; exact hrow a
          _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ = (Fintype.card (LayerSamplerAxis I n) : ℝ) * Real.exp (2 * Q + 1) := by simp
      _ ≤ Real.exp P * Real.exp (2 * Q + 1) := mul_le_mul_of_nonneg_right (hcount _ haxes) (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  have hAlip : (allocatedForecastAllAxisLiftLip B hδ : ℝ) ≤ Real.exp (E + P + 2 * Q + 1) := by
    rw [allocatedForecastAllAxisLiftLip, NNReal.coe_mul]
    calc
      _ ≤ Real.exp E * Real.exp (P + (2 * Q + 1)) := mul_le_mul hA hsum (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hcap : (allocatedForecastAllAxisCap (X := X) B hδ s : ℝ) ≤ Real.exp (F + E) := by
    change ((C ^ Fintype.card X * allocatedForecastAllAxisLiftCap B hδ : ℝ≥0) : ℝ) ≤ _
    rw [NNReal.coe_mul]
    exact (mul_le_mul hC hA (by positivity) (Real.exp_nonneg _)).trans_eq (Real.exp_add _ _).symm
  constructor
  · have hh := one_add_le_exp_succ (by dsimp [E, F]; positivity) hcap
    rw [add_comm 1] at hh
    exact hh
  · have hfirst : (allocatedForecastAllAxisLiftCap B hδ : ℝ) *
        ((Fintype.card X : ℝ) * K * (C ^ Fintype.card X : ℝ≥0)) ≤
          Real.exp (E + P + (4 * P + 2) + F) := by
      calc
        _ ≤ Real.exp E * (Real.exp P * Real.exp (4 * P + 2) * Real.exp F) := by
          gcongr
          exact hcount _ hX
        _ = _ := by simp only [← Real.exp_add]; congr 1; ring
    have hsecond : ((C ^ Fintype.card X : ℝ≥0) : ℝ) *
        allocatedForecastAllAxisLiftLip B hδ ≤ Real.exp (F + E + P + 2 * Q + 1) := by
      calc
        _ ≤ Real.exp F * Real.exp (E + P + 2 * Q + 1) := by gcongr
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hh := add_le_exp_add_one (by dsimp [E, F]; positivity)
      (by dsimp [E, F]; positivity) hfirst hsecond
    change _ ≤ _ at hh
    convert hh using 1
    · simp only [allocatedForecastAllAxisLip, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, C, K]
    · congr 1
      dsimp [forecastOriginalSmoothLipLog, E, F]
      ring

theorem allocatedOriginalForecast_uniform_budget
    {m : ℕ} {G X Z : Type*} [Fintype G] [Fintype X] [Fintype Z]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (s : Empty ↪ Z) {P δ : ℝ} (hP : 1 ≤ P) (hδ : 0 < δ)
    (hδinv : δ⁻¹ ≤ Real.exp P)
    (hX : (Fintype.card X : ℝ) ≤ P) (hZ : (Fintype.card Z : ℝ) ≤ P)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ P)
    (hblocks : (∑ a, (Fintype.card (B a) : ℝ)) ≤ P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) :
    let Q := ((m : ℝ) + 2) * P + 4 * m + 8
    (allocatedOriginalForecastCap (X := X) B U basis S s hδ : ℝ) + 1 ≤
        Real.exp (forecastOriginalSmoothCapLog P Q) ∧
      (allocatedOriginalForecastLip (X := X) B U basis S s hδ : ℝ) ≤
        Real.exp (forecastOriginalSmoothLipLog P Q) := by
  intro Q
  have hP0 : 0 ≤ P := le_trans zero_le_one hP
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hh := forecastAllAxis_budget (X := X) B s hP0 hQ hδ hX hZ haxes hprofile
    (allocatedForecastAllAxisRowCap_le_exp B hP hblocks hδ hδinv)
  constructor
  · have hc : (allocatedOriginalForecastCap (X := X) B U basis S s hδ : ℝ) ≤
        allocatedForecastAllAxisCap (X := X) B hδ s :=
      NNReal.coe_le_coe.mpr (allocatedOriginalForecastCap_le_allAxis (X := X) B hδ s U basis S)
    linarith [hh.1]
  · exact (NNReal.coe_le_coe.mpr (allocatedOriginalForecastLip_le_allAxis (X := X)
      B hδ s U basis S)).trans hh.2

theorem allocatedOriginalForecast_common_budget
    {m : ℕ} {G X Z : Type*} [Fintype G] [Fintype X] [Fintype Z]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (s : Empty ↪ Z) {P δ : ℝ} (hP : 1 ≤ P) (hδ : 0 < δ)
    (hδinv : δ⁻¹ ≤ Real.exp P)
    (hX : (Fintype.card X : ℝ) ≤ P) (hZ : (Fintype.card Z : ℝ) ≤ P)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ P)
    (hblocks : (∑ a, (Fintype.card (B a) : ℝ)) ≤ P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) :
    (allocatedOriginalForecastCap (X := X) B U basis S s hδ : ℝ) + 1 ≤
        Real.exp (forecastOriginalSmoothBudget m P) ∧
      (allocatedOriginalForecastLip (X := X) B U basis S s hδ : ℝ) ≤
        Real.exp (forecastOriginalSmoothBudget m P) := by
  have hh := allocatedOriginalForecast_uniform_budget (X := X) B U basis S s hP hδ
    hδinv hX hZ haxes hblocks hprofile
  have hb := forecastOriginalSmoothBudget_bounds m (zero_le_one.trans hP)
  exact ⟨hh.1.trans (Real.exp_le_exp.mpr hb.2.1),
    hh.2.trans (Real.exp_le_exp.mpr hb.2.2)⟩

end Erdos3.VectorPolynomial

end

end OAI
