import OAI.Combinatorics.Progressions.Estimates.RetainedSlicedCoefficientSource
import OAI.Combinatorics.Progressions.Estimates.UniformProfileRadiusLog

namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal

noncomputable def canonicalAffineMinorLog (O α : Type*) [Fintype O] [Fintype α]
    (h : ℕ) (P E F : ℝ) : ℝ :=
  canonicalBooleanMinorLog O α h P E +
    (cubeMinorVariableCount O α h * cubeMinorDegree O h : ℕ) *
      (cubeMinorVariableCount O α h : ℝ) * F

 theorem canonicalAffineMinorLog_nonneg (O α : Type*) [Fintype O] [Fintype α]
    (h : ℕ) {P E F : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    0 ≤ canonicalAffineMinorLog O α h P E F :=
  add_nonneg (canonicalBooleanMinorLog_nonneg O α h hP hE) (by positivity)

 theorem canonicalAffineCubeMinorThreshold_inverse_le_exp (O α : Type*)
    [Fintype O] [Nonempty O] [Fintype α] [DecidableEq α]
    (h : ℕ) (hh : 0 < h) {c₀ δ η P E F : ℝ}
    (hc₀ : 0 < c₀) (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η)
    (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hcP : c₀⁻¹ ≤ Real.exp P) (hηE : η⁻¹ ≤ Real.exp E) (hδF : δ⁻¹ ≤ Real.exp F) :
    (canonicalAffineCubeMinorThreshold O α h c₀ δ η)⁻¹ ≤ Real.exp (canonicalAffineMinorLog O α h P E F) := by
  have hkpos := canonicalAffineCubeMinorThreshold_pos O α hh hc₀ hδ hη
  have hbasepos := canonicalCubeMinorThreshold_pos Unit O α hh hc₀ hη
  have hbase : (canonicalCubeMinorThreshold Unit O α h c₀ η)⁻¹ ≤
      Real.exp (canonicalBooleanMinorLog O α h P E) := by
    simpa only [Fintype.card_unique, canonicalBooleanMinorLog] using
      canonicalCubeMinorThreshold_inverse_le_exp Unit O α h hh hc₀ hη hP hE hcP hηE
  have hsame : canonicalAffineCubeMinorThreshold O α h c₀ 1 η =
      canonicalCubeMinorThreshold Unit O α h c₀ η := by
    simp only [canonicalAffineCubeMinorThreshold, canonicalCubeMinorThreshold,
      affineCubeMinorThreshold, cubeMinorThreshold, inv_one, one_pow, mul_one]
  have hlbase := Real.log_le_log (inv_pos.mpr hbasepos) hbase
  rw [Real.log_exp] at hlbase
  have hlδ := Real.log_le_log (inv_pos.mpr hδ) hδF
  rw [Real.log_exp] at hlδ
  have he := canonicalAffineCubeMinorThreshold_log_inv_relative O α hh hc₀ hδ hδone hη
  rw [hsame] at he
  have hb : Real.log (canonicalAffineCubeMinorThreshold O α h c₀ δ η)⁻¹ ≤
      canonicalAffineMinorLog O α h P E F := by
    apply he.trans
    exact add_le_add hlbase (mul_le_mul_of_nonneg_left hlδ (by positivity))
  simpa only [Real.exp_log (inv_pos.mpr hkpos)] using Real.exp_le_exp.mpr hb

noncomputable def jointAffineInverseLog {D α : Type*} [Fintype D] [Fintype α]
    {O : D → Type*} [∀ d, Fintype (O d)] (h : D → ℕ) (P E F : ℝ) : ℝ :=
  Fintype.card D + ∑ d, (F + productMinorInverseLog (Fintype.card (O d)) (Fintype.card α) (h d) P
    (canonicalAffineMinorLog (O d) α (h d) P E F))

 theorem jointAffineInverseLog_nonneg {D α : Type*} [Fintype D] [Fintype α]
    {O : D → Type*} [∀ d, Fintype (O d)] (h : D → ℕ) {P E F : ℝ}
    (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    0 ≤ jointAffineInverseLog (O := O) (α := α) h P E F := by
  apply add_nonneg (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro d _
  have hk := canonicalAffineMinorLog_nonneg (O d) α (h d) hP hE hF
  unfold productMinorInverseLog productMinorEntryLog
  positivity

 theorem jointAffineBooleanInverseBudget_le_exp {D α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    {O : D → Type*} [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (c₀ C η : D → ℝ)
    (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d) (hη : ∀ d, 0 < η d)
    {δ P E F : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hcP : ∀ d, (c₀ d)⁻¹ ≤ Real.exp P) (hCP : ∀ d, C d ≤ Real.exp P)
    (hηE : ∀ d, (η d)⁻¹ ≤ Real.exp E) (hδF : δ⁻¹ ≤ Real.exp F) :
    (jointAffineBooleanInverseBudget (O := O) (α := α) h C
      (fun d => canonicalAffineCubeMinorThreshold (O d) α (h d) (c₀ d) δ (η d)) δ : ℝ) ≤
      Real.exp (jointAffineInverseLog (O := O) (α := α) h P E F) := by
  unfold jointAffineBooleanInverseBudget jointAffineInverseLog
  rw [NNReal.coe_sum]
  apply sum_le_exp_card_add_sum
  · intro d
    have hk := canonicalAffineMinorLog_nonneg (O d) α (h d) hP hE hF
    unfold productMinorInverseLog productMinorEntryLog
    positivity
  · intro d
    apply coe_toNNReal_le_exp
    have hb := productMinorInverseBound_le_exp (Fintype.card (O d)) (Fintype.card α) (h d) (hC d)
      (canonicalAffineCubeMinorThreshold_pos (O d) α (hh d) (hc₀ d) hδ (hη d)) (hCP d)
      (canonicalAffineCubeMinorThreshold_inverse_le_exp (O d) α (h d) (hh d)
        (hc₀ d) hδ hδone (hη d) hP hE (hcP d) (hηE d) hδF)
    calc
      _ ≤ Real.exp F * Real.exp _ := mul_le_mul hδF hb
        (productMinorInverseBound_nonneg _ _ _ (hC d) zero_le_one
          (canonicalAffineCubeMinorThreshold_pos (O d) α (hh d) (hc₀ d) hδ (hη d)).le)
        (Real.exp_pos F).le
      _ = _ := (Real.exp_add _ _).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def affineBooleanAxisWeightLog (B O α : Type*) [Fintype B] [Fintype O] [Fintype α]
    (h : ℕ) (P E F : ℝ) : ℝ :=
  (scalarCubeDerivativeLog (Fintype.card α) P+2*Fintype.card (B × Fin h)+E+1)+
  (Fintype.card (BlockParameter B (Fin h) α)+P+canonicalAffineMinorLog O α h P E F+
    productMinorDeterminantLog (Fintype.card (BlockParameter B (Fin h) α))
      (Fintype.card O) (Fintype.card α) h P)+1

noncomputable def jointAffineBooleanWeightLog {D α : Type*} [Fintype D] [Fintype α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (h : D → ℕ) (P E F : ℝ) : ℝ :=
  Fintype.card D + ∑ d, affineBooleanAxisWeightLog (B d) (O d) α (h d) P E F

noncomputable def affineBooleanAxisWeightCost (B O α : Type*) [Fintype B] [Fintype O]
    [Fintype α] [DecidableEq α] (h : ℕ) (C : ℝ) (A T : ℝ≥0) (c₀ δ η : ℝ) : ℝ :=
  (∑ _i : B × Fin h, ((2*2^Fintype.card α : ℕ) : ℝ)*((Fintype.card α : ℝ)+1)^2*T/
    scalarCubeProductBoundaryRadius (B × Fin h) α (η/2))+
  (Fintype.card (BlockParameter B (Fin h) α) : ℝ)*
    ((A : ℝ)/canonicalAffineCubeMinorThreshold O α h c₀ δ η*
      productMinorDeterminantDerivativeBound (Fintype.card (BlockParameter B (Fin h) α))
        (Fintype.card O) (Fintype.card α) h C 1)

theorem affineBooleanAxisWeightLog_nonneg (B O α : Type*) [Fintype B] [Fintype O] [Fintype α]
    (h : ℕ) {P E F : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F) : 0 ≤ affineBooleanAxisWeightLog B O α h P E F := by
  have hk := canonicalAffineMinorLog_nonneg O α h hP hE hF
  unfold affineBooleanAxisWeightLog scalarCubeDerivativeLog scalarCubeBoundaryLog
    productMinorDeterminantLog productMinorPartialLog productMinorEntryLog
  positivity

theorem affineBooleanAxisWeightCost_le_exp (B O α : Type*) [Fintype B] [Fintype O] [Nonempty O]
    [Fintype α] [DecidableEq α] (h : ℕ) (hh : 0 < h) {C c₀ δ η P E F : ℝ}
    (hC : 0 ≤ C) (hc₀ : 0 < c₀) (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hCP : C ≤ Real.exp P) (hcP : c₀⁻¹ ≤ Real.exp P) (hηE : η⁻¹ ≤ Real.exp E) (hδF : δ⁻¹ ≤ Real.exp F)
    (A T : ℝ≥0) (hAP : (A : ℝ) ≤ Real.exp P) (hTP : (T : ℝ) ≤ Real.exp P) :
    affineBooleanAxisWeightCost B O α h C A T c₀ δ η ≤ Real.exp (affineBooleanAxisWeightLog B O α h P E F) := by
  let n := Fintype.card (BlockParameter B (Fin h) α)
  let k := Fintype.card (B × Fin h)
  let b := scalarCubeDerivativeLog (Fintype.card α) P+2*k+E+1
  let m := (n : ℝ)+P+canonicalAffineMinorLog O α h P E F+
    productMinorDeterminantLog n (Fintype.card O) (Fintype.card α) h P
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hhη : (η/2)⁻¹ ≤ Real.exp (E+1) := by
    calc
      _ = 2*η⁻¹ := by rw [inv_div, div_eq_mul_inv]
      _ ≤ Real.exp 1*Real.exp E := by gcongr
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hk : (k : ℝ)+1 ≤ Real.exp k := Real.add_one_le_exp _
  have hd := scalarCubeProductDerivativeConstant_le_exp α T hTP
  have hd0 : 0 ≤ scalarCubeProductDerivativeConstant α T := by
    unfold scalarCubeProductDerivativeConstant
    have := (scalarCubeBoundaryConstant_pos α).le
    positivity
  have hb : (∑ _i : B × Fin h, ((2*2^Fintype.card α : ℕ) : ℝ)*((Fintype.card α : ℝ)+1)^2*T/
      scalarCubeProductBoundaryRadius (B × Fin h) α (η/2)) ≤ Real.exp b := by
    apply (scalarCubeProductBoundaryRadius_derivative (B × Fin h) α T (half_pos hη)).trans
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp (scalarCubeDerivativeLog (Fintype.card α) P)*(Real.exp k)^2*Real.exp (E+1) := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; dsimp [b]; ring
  have hκ : (canonicalAffineCubeMinorThreshold O α h c₀ δ η)⁻¹ ≤
      Real.exp (canonicalAffineMinorLog O α h P E F) := by
    simpa using
      canonicalAffineCubeMinorThreshold_inverse_le_exp O α h hh hc₀ hδ hδone hη hP hE hcP hηE hδF
  have hκ0 := canonicalAffineCubeMinorThreshold_pos O α hh hc₀ hδ hη
  have hdet := productMinorDeterminantDerivativeBound_le_exp n (Fintype.card O) (Fintype.card α) h hC hP hCP
  have hdet0 := productMinorDeterminantDerivativeBound_nonneg n (Fintype.card O) (Fintype.card α) h hC zero_le_one
  have hn : (n : ℝ) ≤ Real.exp n := by linarith [Real.add_one_le_exp (n : ℝ)]
  have hm : (n : ℝ)*((A : ℝ)/canonicalAffineCubeMinorThreshold O α h c₀ δ η*
      productMinorDeterminantDerivativeBound n (Fintype.card O) (Fintype.card α) h C 1) ≤ Real.exp m := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp n*(Real.exp P*Real.exp (canonicalAffineMinorLog O α h P E F)*
          Real.exp (productMinorDeterminantLog n (Fintype.card O) (Fintype.card α) h P)) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; dsimp [m]; ring
  have hb0 : 0 ≤ b := by dsimp [b, scalarCubeDerivativeLog, scalarCubeBoundaryLog]; positivity
  have hm0 : 0 ≤ m := by
    have := canonicalAffineMinorLog_nonneg O α h hP hE hF
    dsimp [m, productMinorDeterminantLog, productMinorPartialLog, productMinorEntryLog]
    positivity
  exact add_le_exp_add_one hb0 hm0 hb hm

theorem jointAffineBooleanWeightLog_nonneg {D α : Type*} [Fintype D] [Fintype α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (h : D → ℕ) {P E F : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    0 ≤ jointAffineBooleanWeightLog (B := B) (O := O) (α := α) h P E F :=
  add_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun d _ => affineBooleanAxisWeightLog_nonneg (B d) (O d) α (h d) hP hE hF))

theorem jointAffineBooleanWeightBudget_canonical_le_exp {D α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (c₀ C η : D → ℝ)
    (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d) (hη : ∀ d, 0 < η d)
    {δ P E F : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hcP : ∀ d, (c₀ d)⁻¹ ≤ Real.exp P) (hCP : ∀ d, C d ≤ Real.exp P)
    (hηE : ∀ d, (η d)⁻¹ ≤ Real.exp E) (hδF : δ⁻¹ ≤ Real.exp F) (A T : ℝ≥0)
    (hAP : (A : ℝ) ≤ Real.exp P) (hTP : (T : ℝ) ≤ Real.exp P) :
    jointBooleanWeightBudget (B := B) (O := O) (α := α) h C A T
      (fun d _ => scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d/2))
      (fun d => canonicalAffineCubeMinorThreshold (O d) α (h d) (c₀ d) δ (η d)) ≤
      Real.exp (jointAffineBooleanWeightLog (B := B) (O := O) (α := α) h P E F) := by
  change (∑ d, affineBooleanAxisWeightCost (B d) (O d) α (h d) (C d) A T (c₀ d) δ (η d)) ≤
    Real.exp ((Fintype.card D : ℝ)+∑ d, affineBooleanAxisWeightLog (B d) (O d) α (h d) P E F)
  exact sum_le_exp_card_add_sum
    (fun d => affineBooleanAxisWeightCost (B d) (O d) α (h d) (C d) A T (c₀ d) δ (η d))
    (fun d => affineBooleanAxisWeightLog (B d) (O d) α (h d) P E F)
    (fun d => affineBooleanAxisWeightLog_nonneg (B d) (O d) α (h d) hP hE hF)
    (fun d => affineBooleanAxisWeightCost_le_exp (B d) (O d) α (h d) (hh d)
      (hC d) (hc₀ d) hδ hδone (hη d) hP hE hF (hCP d) (hcP d) (hηE d) hδF A T hAP hTP)

end Erdos3

end

section

namespace Erdos3

section Definitions
variable {A : Type*} [Semiring A]
def affineMinorVariableEnvelope (D : A) : A := D * (D * (D + 1))
def affineMinorDegreeEnvelope (D : A) : A := 1 + D * D
def affineMinorConstantEnvelope (D : A) : A :=
  D * D * (D + 1)^2 + 3 * affineMinorVariableEnvelope D +
    (affineMinorDegreeEnvelope D + 1) +
    affineMinorDegreeEnvelope D * (8 + (affineMinorDegreeEnvelope D + 1))
def affineMinorLogEnvelope (D P E F : A) : A :=
  affineMinorVariableEnvelope D * affineMinorDegreeEnvelope D + D * P + 2 +
    affineMinorVariableEnvelope D * affineMinorDegreeEnvelope D *
      (affineMinorConstantEnvelope D + 1 + E + 2) +
    affineMinorVariableEnvelope D * affineMinorDegreeEnvelope D * affineMinorVariableEnvelope D * F
end Definitions

 theorem affineMinorVariableEnvelope_nonneg {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ affineMinorVariableEnvelope D := by unfold affineMinorVariableEnvelope; positivity
 theorem affineMinorDegreeEnvelope_nonneg {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ affineMinorDegreeEnvelope D := by unfold affineMinorDegreeEnvelope; positivity
 theorem affineMinorConstantEnvelope_nonneg {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ affineMinorConstantEnvelope D := by
  have := affineMinorVariableEnvelope_nonneg hD
  have := affineMinorDegreeEnvelope_nonneg hD
  unfold affineMinorConstantEnvelope
  positivity
 theorem affineMinorLogEnvelope_nonneg {D P E F : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    0 ≤ affineMinorLogEnvelope D P E F := by
  have := affineMinorVariableEnvelope_nonneg hD
  have := affineMinorDegreeEnvelope_nonneg hD
  have := affineMinorConstantEnvelope_nonneg hD
  unfold affineMinorLogEnvelope
  positivity

 theorem cubeMinor_counts_le_envelope (O α : Type*) [Fintype O] [Fintype α]
    (h : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hO : (Fintype.card O : ℝ) ≤ D) (hα : (Fintype.card α : ℝ) ≤ D) (hh : (h : ℝ) ≤ D) :
    (cubeMinorVariableCount O α h : ℝ) ≤ affineMinorVariableEnvelope D ∧
    (cubeMinorDegree O h : ℝ) ≤ affineMinorDegreeEnvelope D := by
  constructor
  · simp only [cubeMinorVariableCount, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      affineMinorVariableEnvelope]
    gcongr
  · have hs : ((h - 1 : ℕ) : ℝ) ≤ D := (Nat.cast_le.mpr (Nat.sub_le _ _)).trans hh
    simp only [cubeMinorDegree, Nat.cast_max, Nat.cast_one, Nat.cast_mul, affineMinorDegreeEnvelope]
    apply max_le
    · nlinarith [sq_nonneg D]
    · exact (mul_le_mul hO hs (Nat.cast_nonneg _) hD).trans (by linarith)

 theorem canonicalAffineMinorLog_le_envelope (O α : Type*) [Fintype O] [Fintype α]
    (h : ℕ) {D P E F : ℝ} (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hO : (Fintype.card O : ℝ) ≤ D) (hα : (Fintype.card α : ℝ) ≤ D) (hh : (h : ℝ) ≤ D) :
    canonicalAffineMinorLog O α h P E F ≤ affineMinorLogEnvelope D P E F := by
  obtain ⟨hN, hd⟩ := cubeMinor_counts_le_envelope O α h hD hO hα hh
  have hN0 := affineMinorVariableEnvelope_nonneg hD
  have hd0 := affineMinorDegreeEnvelope_nonneg hD
  have hC0 := affineMinorConstantEnvelope_nonneg hD
  have hC : cubeMinorConstantLog (Fintype.card O) (Fintype.card α) h
      (cubeMinorVariableCount O α h) (cubeMinorDegree O h) ≤ affineMinorConstantEnvelope D := by
    unfold cubeMinorConstantLog affineMinorConstantEnvelope
    gcongr
  have hCold : 0 ≤ cubeMinorConstantLog (Fintype.card O) (Fintype.card α) h
      (cubeMinorVariableCount O α h) (cubeMinorDegree O h) := by
    unfold cubeMinorConstantLog
    positivity
  unfold canonicalAffineMinorLog canonicalBooleanMinorLog cubeMinorThresholdLog cubeMinorScaleLog
    affineMinorLogEnvelope
  push_cast
  gcongr

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

variable {D α : Type*} [Fintype D] [Fintype α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

noncomputable def jointAffineTranslationLog (h : D → ℕ) (P E F : ℝ) : ℝ :=
  Fintype.card (Σ d, O d) + Fintype.card (JointBlockParameter B h α) +
    3 * jointAffineInverseLog (O := O) (α := α) h P E F +
    jointBooleanDerivativeLog (B := B) (O := O) (α := α) h P +
    jointAffineBooleanWeightLog (B := B) (O := O) (α := α) h P E F + 1

noncomputable def jointAffinePerturbationLog (h : D → ℕ) (P E F : ℝ) : ℝ :=
  Fintype.card (JointBlockParameter B h α) +
    3 * jointAffineInverseLog (O := O) (α := α) h P E F +
    jointBooleanDerivativeLog (B := B) (O := O) (α := α) h P +
    jointAffineBooleanWeightLog (B := B) (O := O) (α := α) h P E F + 6

 theorem jointAffineDivergence_le_exp [DecidableEq D] [DecidableEq α]
    [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (c₀ C η : D → ℝ)
    (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d) (hη : ∀ d, 0 < η d)
    {δ P E F : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hcP : ∀ d, (c₀ d)⁻¹ ≤ Real.exp P) (hCP : ∀ d, C d ≤ Real.exp P)
    (hηE : ∀ d, (η d)⁻¹ ≤ Real.exp E) (hδF : δ⁻¹ ≤ Real.exp F) (A T : ℝ≥0)
    (hAP : (A : ℝ) ≤ Real.exp P) (hTP : (T : ℝ) ≤ Real.exp P) :
    let r := fun d (_ : B d × Fin (h d)) => scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2)
    let κ := fun d => canonicalAffineCubeMinorThreshold (O d) α (h d) (c₀ d) δ (η d)
    let K := jointAffineBooleanInverseBudget (O := O) (α := α) h C κ δ
    let H := jointBooleanDerivativeBudget (B := B) (O := O) (α := α) h C
    (jointAffineBooleanTranslationBudget (O := O) (α := α) C A T r κ K H : ℝ) ≤
      Real.exp (jointAffineTranslationLog (B := B) (O := O) (α := α) h P E F) ∧
    jointAffineBooleanErrorBudget (O := O) (α := α) h C κ A T r δ ≤
      Real.exp (jointAffinePerturbationLog (B := B) (O := O) (α := α) h P E F) := by
  intro r κ K H
  have hK := jointAffineBooleanInverseBudget_le_exp (O := O) (α := α)
    h hh c₀ C η hc₀ hC hη hδ hδone hP hE hF hcP hCP hηE hδF
  have hH := jointBooleanDerivativeBudget_le_exp (B := B) (O := O) (α := α) h C hC hP hCP
  have hS := jointAffineBooleanWeightBudget_canonical_le_exp (B := B) (O := O) (α := α)
    h hh c₀ C η hc₀ hC hη hδ hδone hP hE hF hcP hCP hηE hδF A T hAP hTP
  have hS0 := jointBooleanWeightBudget_nonneg (B := B) (O := O) (α := α) h C hC A T r
    (fun d _ => (scalarCubeProductBoundaryRadius_pos (B d × Fin (h d)) α (half_pos (hη d))).le)
    κ (fun d => (canonicalAffineCubeMinorThreshold_pos (O d) α (hh d) (hc₀ d) hδ (hη d)).le)
  have hKL := jointAffineInverseLog_nonneg (O := O) (α := α) h hP hE hF
  have hHL := jointBooleanDerivativeLog_nonneg (B := B) (O := O) (α := α) h hP
  have hSL := jointAffineBooleanWeightLog_nonneg (B := B) (O := O) (α := α) h hP hE hF
  constructor
  · have he := translationDivergence_le_exp (Fintype.card (Σ d, O d))
      (Fintype.card (JointBlockParameter B h α)) K.coe_nonneg H.coe_nonneg hS0
      hKL hHL hSL hK hH hS
    simpa only [jointAffineTranslationLog, Nat.cast_add, jointAffineBooleanTranslationBudget, NNReal.coe_mul, NNReal.coe_add,
      NNReal.coe_natCast, NNReal.coe_pow, Real.coe_toNNReal _ hS0] using he
  · exact perturbationDivergence_le_exp (Fintype.card (JointBlockParameter B h α))
      K.coe_nonneg H.coe_nonneg hS0 hKL hHL hSL hK hH hS

end Erdos3

end

section

namespace Erdos3

section Definitions
variable {A : Type*} [Semiring A]
def affineInverseAxisEnvelope (D P E F : A) : A :=
  F + (D + D^2 + D * (P + D + D * D) + affineMinorLogEnvelope D P E F)

def affineDerivativeAxisEnvelope (D P : A) : A :=
  affineMinorVariableEnvelope D + D + (P + 2 * D + D * D)

def affineWeightAxisEnvelope (D P E F : A) : A :=
  (P + 3 * D + 1 + ((D + 1)^2 + 2 * D + 2) + 2 * (D * D) + E + 1) +
    (affineMinorVariableEnvelope D + P + affineMinorLogEnvelope D P E F +
      (affineMinorVariableEnvelope D + D^2 + D + (P + 2 * D + D * D) +
        D * (P + D + D * D + 1))) + 1
end Definitions

 theorem affineInverseAxisEnvelope_nonneg {D P E F : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    0 ≤ affineInverseAxisEnvelope D P E F := by
  have := affineMinorLogEnvelope_nonneg hD hP hE hF
  unfold affineInverseAxisEnvelope
  positivity
 theorem affineDerivativeAxisEnvelope_nonneg {D P : ℝ} (hD : 0 ≤ D) (hP : 0 ≤ P) :
    0 ≤ affineDerivativeAxisEnvelope D P := by
  have := affineMinorVariableEnvelope_nonneg hD
  unfold affineDerivativeAxisEnvelope
  positivity
 theorem affineWeightAxisEnvelope_nonneg {D P E F : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    0 ≤ affineWeightAxisEnvelope D P E F := by
  have := affineMinorLogEnvelope_nonneg hD hP hE hF
  have := affineMinorVariableEnvelope_nonneg hD
  unfold affineWeightAxisEnvelope
  positivity

 theorem affineBlockParameter_card_le (B α : Type*) [Fintype B] [Fintype α]
    (h : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hB : (Fintype.card B : ℝ) ≤ D) (hα : (Fintype.card α : ℝ) ≤ D) (hh : (h : ℝ) ≤ D) :
    (Fintype.card (BlockParameter B (Fin h) α) : ℝ) ≤ affineMinorVariableEnvelope D := by
  simp only [BlockParameter, Fintype.card_prod, Fintype.card_fin, Fintype.card_option,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, affineMinorVariableEnvelope]
  gcongr

 theorem affineInverseAxisLog_le_envelope (O α : Type*) [Fintype O] [Fintype α]
    (h : ℕ) {D P E F : ℝ} (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hO : (Fintype.card O : ℝ) ≤ D) (hα : (Fintype.card α : ℝ) ≤ D) (hh : (h : ℝ) ≤ D) :
    F + productMinorInverseLog (Fintype.card O) (Fintype.card α) h P
      (canonicalAffineMinorLog O α h P E F) ≤ affineInverseAxisEnvelope D P E F := by
  have hminor := canonicalAffineMinorLog_le_envelope O α h hD hP hE hF hO hα hh
  have hj : ((Fintype.card O - 1 : ℕ) : ℝ) ≤ D := (Nat.cast_le.mpr (Nat.sub_le _ _)).trans hO
  unfold productMinorInverseLog productMinorEntryLog affineInverseAxisEnvelope
  gcongr

 theorem affineDerivativeAxisLog_le_envelope (B O α : Type*) [Fintype B] [Fintype O] [Fintype α]
    (h : ℕ) {D P : ℝ} (hD : 0 ≤ D)
    (hB : (Fintype.card B : ℝ) ≤ D) (hO : (Fintype.card O : ℝ) ≤ D)
    (hα : (Fintype.card α : ℝ) ≤ D) (hh : (h : ℝ) ≤ D) :
    productMinorDerivativeLog (Fintype.card (BlockParameter B (Fin h) α))
      (Fintype.card O) (Fintype.card α) h P ≤ affineDerivativeAxisEnvelope D P := by
  have hn := affineBlockParameter_card_le B α h hD hB hα hh
  unfold productMinorDerivativeLog productMinorPartialLog affineDerivativeAxisEnvelope
  gcongr

 theorem affineWeightAxisLog_le_envelope (B O α : Type*) [Fintype B] [Fintype O] [Fintype α]
    (h : ℕ) {D P E F : ℝ} (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hB : (Fintype.card B : ℝ) ≤ D) (hO : (Fintype.card O : ℝ) ≤ D)
    (hα : (Fintype.card α : ℝ) ≤ D) (hh : (h : ℝ) ≤ D) :
    affineBooleanAxisWeightLog B O α h P E F ≤ affineWeightAxisEnvelope D P E F := by
  have hn := affineBlockParameter_card_le B α h hD hB hα hh
  have hminor := canonicalAffineMinorLog_le_envelope O α h hD hP hE hF hO hα hh
  have hbh : (Fintype.card (B × Fin h) : ℝ) ≤ D * D := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    exact mul_le_mul hB hh (Nat.cast_nonneg _) hD
  unfold affineBooleanAxisWeightLog affineWeightAxisEnvelope scalarCubeDerivativeLog scalarCubeBoundaryLog
    productMinorDeterminantLog productMinorPartialLog productMinorEntryLog
  gcongr

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]

noncomputable def jointAffineSourceInputLog (h : D → ℕ) (P E F : ℝ) : ℝ :=
  jointAffineTranslationLog (B := B) (O := O) (α := α) h P E F +
    jointAffinePerturbationLog (B := B) (O := O) (α := α) h P E F +
    jointAffineInverseLog (O := O) (α := α) h P E F + Fintype.card (Σ d, O d) + E + 4

 theorem jointAffineSourceScales_log_bounds (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (A T : ℝ≥0) {δ ε P E F : ℝ}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hε : 0 < ε) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hcP : ∀ d, (c₀ d)⁻¹ ≤ Real.exp P) (hCP : ∀ d, C d ≤ Real.exp P)
    (hAP : (A : ℝ) ≤ Real.exp P) (hTP : (T : ℝ) ≤ Real.exp P)
    (hηE : (ε / (12 * ((Fintype.card D : ℝ) + 1)))⁻¹ ≤ Real.exp E)
    (hεE : (ε / 3)⁻¹ ≤ Real.exp E) (hδF : δ⁻¹ ≤ Real.exp F) :
    let Qlog := jointAffineSourceInputLog (B := B) (O := O) (α := α) h P E F
    0 ≤ Qlog ∧
    (jointAffineSourceRadius (B := B) (O := O) (α := α) h c₀ C A T δ ε)⁻¹ ≤ Real.exp (2 * Qlog + 2) ∧
    Real.log (jointAffineSourceTolerance (B := B) (O := O) (α := α) h c₀ C A T δ ε)⁻¹ ≤
      Real.log 16 + 6 * Qlog := by
  intro Qlog
  let η : D → ℝ := fun _ => ε / (12 * ((Fintype.card D : ℝ) + 1))
  have hη : ∀ d, 0 < η d := fun _ => div_pos hε (by positivity)
  let r := jointAffineSourceBoundaryRadius (B := B) (α := α) h ε
  let κ := jointAffineSourceMinorThreshold (O := O) (α := α) h c₀ δ ε
  let K := jointAffineBooleanInverseBudget (O := O) (α := α) h C κ δ
  let H := jointBooleanDerivativeBudget (B := B) (O := O) (α := α) h C
  let Q := jointAffineBooleanErrorBudget (O := O) (α := α) h C κ A T r δ
  let L := jointAffineBooleanTranslationBudget (O := O) (α := α) C A T r κ K H
  have hdiv := jointAffineDivergence_le_exp (B := B) (O := O) (α := α) h hh c₀ C η hc₀ hC hη
    hδ hδone hP hE hF hcP hCP (fun _ => hηE) hδF A T hAP hTP
  have hk := jointAffineBooleanInverseBudget_le_exp (O := O) (α := α) h hh c₀ C η hc₀ hC hη
    hδ hδone hP hE hF hcP hCP (fun _ => hηE) hδF
  have hKL := jointAffineInverseLog_nonneg (O := O) (α := α) h hP hE hF
  have hHL := jointBooleanDerivativeLog_nonneg (B := B) (O := O) (α := α) h hP
  have hSL := jointAffineBooleanWeightLog_nonneg (B := B) (O := O) (α := α) h hP hE hF
  have hLL : 0 ≤ jointAffineTranslationLog (B := B) (O := O) (α := α) h P E F := by
    unfold jointAffineTranslationLog
    positivity
  have hQL : 0 ≤ jointAffinePerturbationLog (B := B) (O := O) (α := α) h P E F := by
    unfold jointAffinePerturbationLog
    positivity
  have hQlog : 0 ≤ Qlog := by dsimp [Qlog, jointAffineSourceInputLog]; positivity
  have hLlog : jointAffineTranslationLog (B := B) (O := O) (α := α) h P E F ≤ Qlog := by
    dsimp [Qlog, jointAffineSourceInputLog]; linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (Σ d, O d))]
  have hKlog : jointAffineInverseLog (O := O) (α := α) h P E F + 1 ≤ Qlog := by
    dsimp [Qlog, jointAffineSourceInputLog]; linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (Σ d, O d))]
  have hQlog' : jointAffinePerturbationLog (B := B) (O := O) (α := α) h P E F + 1 ≤ Qlog := by
    dsimp [Qlog, jointAffineSourceInputLog]; linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (Σ d, O d))]
  have hElog : E ≤ Qlog := by
    dsimp [Qlog, jointAffineSourceInputLog]; linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (Σ d, O d))]
  have hnlog : (Fintype.card (Σ d, O d) : ℝ) ≤ Qlog := by
    dsimp [Qlog, jointAffineSourceInputLog]; linarith
  have honeLog : 1 ≤ Qlog := by
    dsimp [Qlog, jointAffineSourceInputLog]; linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (Σ d, O d))]
  have hLexp : (L : ℝ) ≤ Real.exp Qlog := hdiv.1.trans (Real.exp_le_exp.mpr hLlog)
  have hKexp : 1 + (K : ℝ) ≤ Real.exp Qlog :=
    (one_add_le_exp_succ hKL hk).trans (Real.exp_le_exp.mpr hKlog)
  have hQexp : 1 + Q ≤ Real.exp Qlog :=
    (one_add_le_exp_succ hQL hdiv.2).trans (Real.exp_le_exp.mpr hQlog')
  have hτexp : (ε / 3)⁻¹ ≤ Real.exp Qlog := hεE.trans (Real.exp_le_exp.mpr hElog)
  have hS0 := jointBooleanWeightBudget_nonneg (B := B) (O := O) (α := α) h C hC A T r
    (fun d _ => (scalarCubeProductBoundaryRadius_pos _ _ (half_pos (hη d))).le)
    κ (fun d => (canonicalAffineCubeMinorThreshold_pos (O d) α (hh d) (hc₀ d) hδ (hη d)).le)
  have hQ : 0 ≤ Q := by dsimp [Q, jointAffineBooleanErrorBudget]; positivity
  refine ⟨hQlog, ?_, ?_⟩
  · have hε' : 0 < 2 * ε / 3 := by positivity
    have hε'exp : (2 * ε / 3)⁻¹ ≤ Real.exp Qlog :=
      (inv_anti₀ (by positivity : 0 < ε / 3) (by linarith : ε / 3 ≤ 2 * ε / 3)).trans hτexp
    have he := regularizationRadius_inverse_le_exp L.coe_nonneg hε' hQlog hLexp hε'exp
    have heq : jointAffineSourceRadius (B := B) (O := O) (α := α) h c₀ C A T δ ε =
        regularizationRadius L (2 * ε / 3) := by
      change min 1 (ε / (3 * (1 + (L : ℝ)))) = min 1 ((2 * ε / 3) / (2 * (1 + (L : ℝ))))
      congr 1
      field_simp
    rwa [heq]
  · exact polynomialPerturbationScale_log_inv_le K.coe_nonneg zero_le_one hQ
      (by positivity : 0 < ε / 3) hQlog (Fintype.card (Σ d, O d)) hKexp
      ((by linarith [Real.add_one_le_exp (1 : ℝ)] : (1 : ℝ) + 1 ≤ Real.exp 1).trans
        (Real.exp_le_exp.mpr honeLog)) hQexp
      ((Real.add_one_le_exp _).trans (Real.exp_le_exp.mpr hnlog)) hτexp

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

variable {D α Z : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  [Fintype Z] [DecidableEq Z]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]

omit [DecidableEq D] [∀ index, DecidableEq (B index)] [∀ index, DecidableEq (O index)] in
 theorem jointAffineSourceTolerance_pos (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (A T : ℝ≥0) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    0 < jointAffineSourceTolerance (B := B) (O := O) (α := α) h c₀ C A T δ ε := by
  let η : D → ℝ := fun _ => ε / (12 * ((Fintype.card D : ℝ) + 1))
  have hη : ∀ d, 0 < η d := fun _ => div_pos hε (by positivity)
  let r := jointAffineSourceBoundaryRadius (B := B) (α := α) h ε
  let κ := jointAffineSourceMinorThreshold (O := O) (α := α) h c₀ δ ε
  have hS0 := jointBooleanWeightBudget_nonneg (B := B) (O := O) (α := α) h C hC A T r
    (fun d _ => (scalarCubeProductBoundaryRadius_pos _ _ (half_pos (hη d))).le)
    κ (fun d => (canonicalAffineCubeMinorThreshold_pos (O d) α (hh d) (hc₀ d) hδ (hη d)).le)
  have hQ : 0 ≤ jointAffineBooleanErrorBudget (O := O) (α := α) h C κ A T r δ := by
    unfold jointAffineBooleanErrorBudget
    positivity
  exact (polynomialPerturbationScale_spec (NNReal.coe_nonneg _) zero_le_one hQ
    (by positivity : 0 < ε / 3) (Fintype.card (Σ d, O d))).1

omit [DecidableEq Z] in
 theorem jointAffineCoefficientTolerance_log_bound (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (A T : ℝ≥0) (degree : ℕ) {Csum Wsum δ ε P E F : ℝ}
    (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum) (hCsumP : Csum ≤ Real.exp P) (hWsumP : Wsum ≤ Real.exp P)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hε : 0 < ε) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hcP : ∀ d, (c₀ d)⁻¹ ≤ Real.exp P) (hCP : ∀ d, C d ≤ Real.exp P)
    (hAP : (A : ℝ) ≤ Real.exp P) (hTP : (T : ℝ) ≤ Real.exp P)
    (hηE : (ε / (12 * ((Fintype.card D : ℝ) + 1)))⁻¹ ≤ Real.exp E)
    (hεE : (ε / 3)⁻¹ ≤ Real.exp E) (hδF : δ⁻¹ ≤ Real.exp F) :
    Real.log (jointAffineCoefficientTolerance (Z := Z) (B := B) (O := O) (α := α)
      h c₀ C A T degree Csum Wsum δ ε)⁻¹ ≤
      Real.log 16 + 6 * jointAffineSourceInputLog (B := B) (O := O) (α := α) h P E F +
        booleanToleranceC2Log (B := B) (α := α) Z h degree P + 1 := by
  let t := jointAffineSourceTolerance (B := B) (O := O) (α := α) h c₀ C A T δ ε
  let M := booleanToleranceC2 (B := B) (α := α) Z h degree Csum Wsum
  have ht : 0 < t := jointAffineSourceTolerance_pos h hh c₀ C hc₀ hC A T hδ hε
  have hM : 0 ≤ M := polynomialC2BoxBudget_nonneg _ _
    (add_nonneg (booleanJetMassBudget_nonneg _ _ hCsum) (booleanJetMassBudget_nonneg _ _ hWsum))
  have hraw := (jointAffineSourceScales_log_bounds (B := B) (O := O) (α := α) h hh c₀ C hc₀ hC A T hδ hδone hε hP hE hF
    hcP hCP hAP hTP hηE hεE hδF).2.2
  have hMexp := booleanToleranceC2_le_exp (B := B) (α := α) Z h degree hCsum hWsum hP hCsumP hWsumP
  have hMlog := Real.log_le_log (by positivity : 0 < 1 + M)
    (one_add_le_exp_succ (booleanToleranceC2Log_nonneg (B := B) (α := α) Z h degree hP) hMexp)
  rw [Real.log_exp] at hMlog
  change Real.log (t / (1 + M))⁻¹ ≤ _
  rw [inv_div, div_eq_mul_inv, Real.log_mul (by positivity : (1 + M : ℝ) ≠ 0) (inv_ne_zero ht.ne')]
  linarith

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

section Definitions
variable {A : Type*} [Semiring A]
def jointAffineInverseEnvelope (D P E F : A) : A := D + D * affineInverseAxisEnvelope D P E F
def jointAffineDerivativeEnvelope (D P : A) : A := D + D * affineDerivativeAxisEnvelope D P
def jointAffineWeightEnvelope (D P E F : A) : A := D + D * affineWeightAxisEnvelope D P E F
def jointAffineSourceEnvelope (D P E F : A) : A :=
  let out := D * D
  let param := D * affineMinorVariableEnvelope D
  let inv := jointAffineInverseEnvelope D P E F
  let deriv := jointAffineDerivativeEnvelope D P
  let weight := jointAffineWeightEnvelope D P E F
  (out + param + 3 * inv + deriv + weight + 1) +
    (param + 3 * inv + deriv + weight + 6) + inv + out + E + 4
end Definitions

 theorem affineLog_sum_le {ι : Type*} [Fintype ι] (f : ι → ℝ) {D C : ℝ}
    (hD : (Fintype.card ι : ℝ) ≤ D) (hC : 0 ≤ C) (hf : ∀ i, f i ≤ C) :
    (∑ i, f i) ≤ D * C := by
  calc
    _ ≤ ∑ _i : ι, C := Finset.sum_le_sum (fun i _ => hf i)
    _ = Fintype.card ι * C := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hD hC

variable {ι α : Type*} [Fintype ι] [Fintype α]
  {B O : ι → Type*} [∀ i, Fintype (B i)] [∀ i, Fintype (O i)]

 theorem jointAffineSourceInputLog_le_envelope (h : ι → ℕ) {D P E F : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (haxes : (Fintype.card ι : ℝ) ≤ D) (hα : (Fintype.card α : ℝ) ≤ D)
    (hB : ∀ i, (Fintype.card (B i) : ℝ) ≤ D)
    (hO : ∀ i, (Fintype.card (O i) : ℝ) ≤ D) (hh : ∀ i, (h i : ℝ) ≤ D) :
    jointAffineSourceInputLog (B := B) (O := O) (α := α) h P E F ≤ jointAffineSourceEnvelope D P E F := by
  have hInv : jointAffineInverseLog (O := O) (α := α) h P E F ≤ jointAffineInverseEnvelope D P E F := by
    apply add_le_add haxes
    exact affineLog_sum_le _ haxes (affineInverseAxisEnvelope_nonneg hD hP hE hF)
      (fun i => affineInverseAxisLog_le_envelope (O i) α (h i) hD hP hE hF (hO i) hα (hh i))
  have hDer : jointBooleanDerivativeLog (B := B) (O := O) (α := α) h P ≤ jointAffineDerivativeEnvelope D P := by
    apply add_le_add haxes
    exact affineLog_sum_le _ haxes (affineDerivativeAxisEnvelope_nonneg hD hP)
      (fun i => affineDerivativeAxisLog_le_envelope (B i) (O i) α (h i) hD (hB i) (hO i) hα (hh i))
  have hWeight : jointAffineBooleanWeightLog (B := B) (O := O) (α := α) h P E F ≤ jointAffineWeightEnvelope D P E F := by
    apply add_le_add haxes
    exact affineLog_sum_le _ haxes (affineWeightAxisEnvelope_nonneg hD hP hE hF)
      (fun i => affineWeightAxisLog_le_envelope (B i) (O i) α (h i) hD hP hE hF (hB i) (hO i) hα (hh i))
  have hOut : (Fintype.card (Σ i, O i) : ℝ) ≤ D * D := by
    simp only [Fintype.card_sigma, Nat.cast_sum]
    exact affineLog_sum_le _ haxes hD hO
  have hParam : (Fintype.card (JointBlockParameter B h α) : ℝ) ≤ D * affineMinorVariableEnvelope D := by
    simp only [JointBlockParameter, Fintype.card_sigma, Nat.cast_sum]
    exact affineLog_sum_le _ haxes (affineMinorVariableEnvelope_nonneg hD)
      (fun i => affineBlockParameter_card_le (B i) α (h i) hD (hB i) hα (hh i))
  unfold jointAffineSourceInputLog jointAffineTranslationLog jointAffinePerturbationLog jointAffineSourceEnvelope
  push_cast
  gcongr

 theorem jointAffineSourceEnvelope_nonneg {D P E F : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    0 ≤ jointAffineSourceEnvelope D P E F := by
  have := affineMinorVariableEnvelope_nonneg hD
  have := affineInverseAxisEnvelope_nonneg hD hP hE hF
  have := affineDerivativeAxisEnvelope_nonneg hD hP
  have := affineWeightAxisEnvelope_nonneg hD hP hE hF
  unfold jointAffineSourceEnvelope jointAffineInverseEnvelope jointAffineDerivativeEnvelope jointAffineWeightEnvelope
  positivity

 theorem jointAffineSourceEnvelope_mono {D P P' E E' F F' : ℝ}
    (hD : 0 ≤ D) (hP : P ≤ P') (hE : E ≤ E') (hF : F ≤ F') :
    jointAffineSourceEnvelope D P E F ≤ jointAffineSourceEnvelope D P' E' F' := by
  dsimp only [jointAffineSourceEnvelope, jointAffineInverseEnvelope, jointAffineDerivativeEnvelope, jointAffineWeightEnvelope,
    affineInverseAxisEnvelope, affineDerivativeAxisEnvelope, affineWeightAxisEnvelope, affineMinorLogEnvelope,
    affineMinorVariableEnvelope, affineMinorDegreeEnvelope]
  gcongr

end Erdos3

end

section

namespace Erdos3
open scoped NNReal Classical

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
  {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)]

noncomputable def partitionedAffineSourceRadius (A T : ℝ≥0) (δ E : ℝ) : ℝ :=
  jointAffineSourceRadius (B := fun d : {d // ¬P d} => B d.val) (O := O) (α := α)
    (fun d => h d.val) (fun d => unitProfilePrincipalSize (B := B) d.val)
    (fun d => 2 * unitProfilePrincipalSize (B := B) d.val) A T δ E

noncomputable def partitionedAffineSourceTolerance (A T : ℝ≥0) (degree : ℕ) (δ E : ℝ) : ℝ :=
  jointAffineCoefficientTolerance (Z := PartitionedProfileNoiseIndex G Z α B h P)
    (B := fun d : {d // ¬P d} => B d.val) (O := O) (α := α)
    (fun d => h d.val) (fun d => unitProfilePrincipalSize (B := B) d.val)
    (fun d => 2 * unitProfilePrincipalSize (B := B) d.val) A T degree 1 1 δ E

end Erdos3

end

section

namespace Erdos3
open scoped NNReal BigOperators Classical

 theorem affineDividedAccuracy_bounds (d : ℕ) {ε E : ℝ} (hε : 0 < ε)
    (hεE : ε⁻¹ ≤ Real.exp E) :
    (ε / (12 * ((d : ℝ) + 1)))⁻¹ ≤ Real.exp (E + d + 4) ∧
    (ε / 3)⁻¹ ≤ Real.exp (E + d + 4) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h12 : (12 : ℝ) ≤ Real.exp 4 := by
    calc
      _ ≤ (2 : ℝ) ^ 4 := by norm_num
      _ ≤ (Real.exp 1) ^ 4 := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  constructor
  · rw [inv_div, div_eq_mul_inv]
    calc
      _ ≤ (Real.exp 4 * Real.exp d) * Real.exp E := by
        gcongr
        exact Real.add_one_le_exp _
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  · rw [inv_div, div_eq_mul_inv]
    calc
      _ ≤ Real.exp 2 * Real.exp E := by
        gcongr
        linarith [Real.add_one_le_exp (2 : ℝ)]
      _ = Real.exp (2 + E) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg (α := ℝ) d])

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
  {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]

 theorem partitionedAffineSource_scales_log_bounds (hh : ∀ d, 0 < h d)
    (A T : ℝ≥0) (degree : ℕ) {δ ε E F : ℝ}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hε : 0 < ε) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hεE : ε⁻¹ ≤ Real.exp E) (hδF : δ⁻¹ ≤ Real.exp F) :
    let Clog := unitProfileCoefficientLog (B := B) A T
    let Elog := E + Fintype.card {d // ¬P d} + 4
    let Qlog := jointAffineSourceInputLog (B := fun d : {d // ¬P d} => B d.val)
      (O := O) (α := α) (fun d => h d.val) Clog Elog F
    (partitionedAffineSourceRadius (B := B) (O := O) (α := α) h P A T δ ε)⁻¹ ≤ Real.exp (2 * Qlog + 2) ∧
    Real.log (partitionedAffineSourceTolerance (G := G) (Z := Z) (B := B) (O := O) (α := α)
      h P A T degree δ ε)⁻¹ ≤ Real.log 16 + 6 * Qlog +
        booleanToleranceC2Log (B := fun d : {d // ¬P d} => B d.val) (α := α)
          (PartitionedProfileNoiseIndex G Z α B h P) (fun d => h d.val) degree Clog + 1 := by
  intro Clog Elog Qlog
  have hC := unitProfileCoefficientLog_bounds (B := B) A T
  have hClog : 0 ≤ Clog := unitProfileCoefficientLog_nonneg (B := B) A T
  have hElog : 0 ≤ Elog := by dsimp [Elog]; positivity
  have hacc := affineDividedAccuracy_bounds (Fintype.card {d // ¬P d}) hε hεE
  have hlow (d : {d // ¬P d}) := unitProfilePrincipalSize_pos (B := B) d.val
  have hupp (d : {d // ¬P d}) : 0 ≤ 2 * unitProfilePrincipalSize (B := B) d.val :=
    mul_nonneg (by norm_num) (hlow d).le
  have hraw := jointAffineSourceScales_log_bounds (B := fun d : {d // ¬P d} => B d.val)
    (O := O) (α := α) (fun d => h d.val) (fun d => hh d.val)
    (fun d => unitProfilePrincipalSize (B := B) d.val) (fun d => 2 * unitProfilePrincipalSize (B := B) d.val)
    hlow hupp A T hδ hδone hε hClog hElog hF
    (fun d => hC.1 d.val) (fun d => hC.2.1 d.val) hC.2.2.1 hC.2.2.2 hacc.1 hacc.2 hδF
  refine ⟨hraw.2.1, ?_⟩
  exact jointAffineCoefficientTolerance_log_bound (Z := PartitionedProfileNoiseIndex G Z α B h P)
    (B := fun d : {d // ¬P d} => B d.val) (O := O) (α := α)
    (fun d => h d.val) (fun d => hh d.val)
    (fun d => unitProfilePrincipalSize (B := B) d.val) (fun d => 2 * unitProfilePrincipalSize (B := B) d.val)
    hlow hupp A T degree zero_le_one zero_le_one (Real.one_le_exp hClog) (Real.one_le_exp hClog)
    hδ hδone hε hClog hElog hF (fun d => hC.1 d.val) (fun d => hC.2.1 d.val)
    hC.2.2.1 hC.2.2.2 hacc.1 hacc.2 hδF

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators NNReal Classical

section Definitions
variable {A : Type*} [Semiring A]
def affineProfileCoefficientEnvelope (D A₀ T₀ : A) : A := D * D + A₀ + T₀ + 7
def affineProfileInputEnvelope (D A₀ T₀ E F : A) : A :=
  jointAffineSourceEnvelope D (affineProfileCoefficientEnvelope D A₀ T₀) (E + D + 4) F

def affineProfileToleranceEnvelope (degree : ℕ) (D N A₀ T₀ E F : A) : A :=
  16 + 6 * affineProfileInputEnvelope D A₀ T₀ E F +
    (3 * N * (degree + 2 : ℕ) +
      (2 * (D + affineProfileCoefficientEnvelope D A₀ T₀ + degree * D) + 1)) + 1
end Definitions

variable {ι G Z α : Type*} [Fintype ι] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
  {B O : ι → Type*} [∀ i, Fintype (B i)] [∀ i, Fintype (O i)]

omit [DecidableEq α] in
 theorem partitionedAffineInputLog_le_envelope (h : ι → ℕ) (partition : ι → Prop)
    (A T : ℝ≥0) {D E F : ℝ} (hD : 0 ≤ D)
    (haxes : (Fintype.card ι : ℝ) ≤ D) (hα : (Fintype.card α : ℝ) ≤ D)
    (hB : ∀ i, (Fintype.card (B i) : ℝ) ≤ D)
    (hO : ∀ i, (Fintype.card (O i) : ℝ) ≤ D) (hh : ∀ i, (h i : ℝ) ≤ D)
    (hE : 0 ≤ E) (hF : 0 ≤ F) :
    jointAffineSourceInputLog (B := fun i : {i // ¬partition i} => B i.val)
      (O := fun i : {i // ¬partition i} => O i.val) (α := α) (fun i => h i.val)
      (unitProfileCoefficientLog (B := B) A T) (E + Fintype.card {i // ¬partition i} + 4) F ≤
        affineProfileInputEnvelope D (A : ℝ) (T : ℝ) E F := by
  have ha : (Fintype.card {i // ¬partition i} : ℝ) ≤ D :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans haxes
  have hC : unitProfileCoefficientLog (B := B) A T ≤ affineProfileCoefficientEnvelope D (A : ℝ) (T : ℝ) := by
    unfold unitProfileCoefficientLog affineProfileCoefficientEnvelope
    gcongr
    exact affineLog_sum_le _ haxes hD hB
  have hb := jointAffineSourceInputLog_le_envelope (B := fun i : {i // ¬partition i} => B i.val)
    (O := fun i : {i // ¬partition i} => O i.val) (α := α) (fun i => h i.val)
    (E := E + Fintype.card {i // ¬partition i} + 4) hD (unitProfileCoefficientLog_nonneg (B := B) A T) (by positivity) hF ha hα
    (fun i => hB i.val) (fun i => hO i.val) (fun i => hh i.val)
  exact hb.trans (jointAffineSourceEnvelope_mono (E' := E + D + 4) hD hC (by linarith) le_rfl)

omit [DecidableEq α] in
 theorem partitionedAffineToleranceLog_le_envelope (h : ι → ℕ) (partition : ι → Prop)
    (A T : ℝ≥0) (degree : ℕ) {D N E F : ℝ} (hD : 0 ≤ D)
    (haxes : (Fintype.card ι : ℝ) ≤ D) (hα : (Fintype.card α : ℝ) ≤ D)
    (hB : ∀ i, (Fintype.card (B i) : ℝ) ≤ D)
    (hO : ∀ i, (Fintype.card (O i) : ℝ) ≤ D) (hh : ∀ i, (h i : ℝ) ≤ D)
    (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hN : (Fintype.card (PolynomialParameter (Z ⊕ (Σ i, SamplerCoefficientSlot G B h i))
      (JointBlockParameter B h α)) : ℝ) ≤ N) :
    let P := unitProfileCoefficientLog (B := B) A T
    let Q := jointAffineSourceInputLog (B := fun i : {i // ¬partition i} => B i.val)
      (O := fun i : {i // ¬partition i} => O i.val) (α := α) (fun i => h i.val)
      P (E + Fintype.card {i // ¬partition i} + 4) F
    Real.log 16 + 6 * Q +
      booleanToleranceC2Log (B := fun i : {i // ¬partition i} => B i.val) (α := α)
        (PartitionedProfileNoiseIndex G Z α B h partition) (fun i => h i.val) degree P + 1 ≤
      affineProfileToleranceEnvelope degree D N (A : ℝ) (T : ℝ) E F := by
  intro P Q
  have hQ := partitionedAffineInputLog_le_envelope (B := B) (O := O) (α := α)
    h partition A T hD haxes hα hB hO hh hE hF
  have hC : P ≤ affineProfileCoefficientEnvelope D (A : ℝ) (T : ℝ) := by
    unfold P unitProfileCoefficientLog affineProfileCoefficientEnvelope
    gcongr
    exact affineLog_sum_le _ haxes hD hB
  have hlog : Real.log 16 ≤ (16 : ℝ) := Real.log_le_self (by norm_num)
  have hc2 : booleanToleranceC2Log (B := fun i : {i // ¬partition i} => B i.val) (α := α)
      (PartitionedProfileNoiseIndex G Z α B h partition) (fun i => h i.val) degree P ≤
      3 * N * (degree + 2 : ℕ) +
        (2 * (D + affineProfileCoefficientEnvelope D (A : ℝ) (T : ℝ) + degree * D) + 1) := by
    unfold booleanToleranceC2Log booleanJetMassLog
    rw [partitionedPolynomialParameter_card]
    gcongr
  exact add_le_add (add_le_add (add_le_add hlog (mul_le_mul_of_nonneg_left hQ (by norm_num))) hc2) le_rfl

end Erdos3

end

end OAI
