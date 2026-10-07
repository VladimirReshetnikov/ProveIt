import OAI.Combinatorics.Progressions.Dynamics.BooleanCanonicalLogBudget
import OAI.Combinatorics.Progressions.Dynamics.JointBooleanWeightBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def booleanAxisWeightCost (B O α : Type*) [Fintype B] [Fintype O]
    [Fintype α] [DecidableEq α] (h : ℕ) (C : ℝ) (A T : ℝ≥0) (c₀ η : ℝ) : ℝ :=
  (∑ _i : B × Fin h, ((2*2^Fintype.card α : ℕ) : ℝ)*((Fintype.card α : ℝ)+1)^2*T/
    scalarCubeProductBoundaryRadius (B × Fin h) α (η/2))+
  (Fintype.card (BlockParameter B (Fin h) α) : ℝ)*
    ((A : ℝ)/canonicalCubeMinorThreshold Unit O α h c₀ η*
      productMinorDeterminantDerivativeBound (Fintype.card (BlockParameter B (Fin h) α))
        (Fintype.card O) (Fintype.card α) h C 1)

theorem booleanAxisWeightLog_nonneg (B O α : Type*) [Fintype B] [Fintype O] [Fintype α]
    (h : ℕ) {P E : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) : 0 ≤ booleanAxisWeightLog B O α h P E := by
  have hk := canonicalBooleanMinorLog_nonneg O α h hP hE
  unfold booleanAxisWeightLog scalarCubeDerivativeLog scalarCubeBoundaryLog
    productMinorDeterminantLog productMinorPartialLog productMinorEntryLog
  positivity

theorem booleanAxisWeightCost_le_exp (B O α : Type*) [Fintype B] [Fintype O] [Nonempty O]
    [Fintype α] [DecidableEq α] (h : ℕ) (hh : 0 < h) {C c₀ η P E : ℝ}
    (hC : 0 ≤ C) (hc₀ : 0 < c₀) (hη : 0 < η) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hCP : C ≤ Real.exp P) (hcP : c₀⁻¹ ≤ Real.exp P) (hηE : η⁻¹ ≤ Real.exp E)
    (A T : ℝ≥0) (hAP : (A : ℝ) ≤ Real.exp P) (hTP : (T : ℝ) ≤ Real.exp P) :
    booleanAxisWeightCost B O α h C A T c₀ η ≤ Real.exp (booleanAxisWeightLog B O α h P E) := by
  let n := Fintype.card (BlockParameter B (Fin h) α)
  let k := Fintype.card (B × Fin h)
  let b := scalarCubeDerivativeLog (Fintype.card α) P+2*k+E+1
  let m := (n : ℝ)+P+canonicalBooleanMinorLog O α h P E+
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
  have hκ : (canonicalCubeMinorThreshold Unit O α h c₀ η)⁻¹ ≤
      Real.exp (canonicalBooleanMinorLog O α h P E) := by
    simpa [canonicalBooleanMinorLog] using
      canonicalCubeMinorThreshold_inverse_le_exp Unit O α h hh hc₀ hη hP hE hcP hηE
  have hκ0 := canonicalCubeMinorThreshold_pos Unit O α hh hc₀ hη
  have hdet := productMinorDeterminantDerivativeBound_le_exp n (Fintype.card O) (Fintype.card α) h hC hP hCP
  have hdet0 := productMinorDeterminantDerivativeBound_nonneg n (Fintype.card O) (Fintype.card α) h hC zero_le_one
  have hn : (n : ℝ) ≤ Real.exp n := by linarith [Real.add_one_le_exp (n : ℝ)]
  have hm : (n : ℝ)*((A : ℝ)/canonicalCubeMinorThreshold Unit O α h c₀ η*
      productMinorDeterminantDerivativeBound n (Fintype.card O) (Fintype.card α) h C 1) ≤ Real.exp m := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp n*(Real.exp P*Real.exp (canonicalBooleanMinorLog O α h P E)*
          Real.exp (productMinorDeterminantLog n (Fintype.card O) (Fintype.card α) h P)) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; dsimp [m]; ring
  have hb0 : 0 ≤ b := by dsimp [b, scalarCubeDerivativeLog, scalarCubeBoundaryLog]; positivity
  have hm0 : 0 ≤ m := by
    have := canonicalBooleanMinorLog_nonneg O α h hP hE
    dsimp [m, productMinorDeterminantLog, productMinorPartialLog, productMinorEntryLog]
    positivity
  exact add_le_exp_add_one hb0 hm0 hb hm

theorem jointBooleanWeightLog_nonneg {D α : Type*} [Fintype D] [Fintype α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (h : D → ℕ) {P E : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) :
    0 ≤ jointBooleanWeightLog (B := B) (O := O) (α := α) h P E :=
  add_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun d _ => booleanAxisWeightLog_nonneg (B d) (O d) α (h d) hP hE))

theorem jointBooleanWeightBudget_canonical_le_exp {D α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (c₀ C η : D → ℝ)
    (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d) (hη : ∀ d, 0 < η d)
    {P E : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hcP : ∀ d, (c₀ d)⁻¹ ≤ Real.exp P) (hCP : ∀ d, C d ≤ Real.exp P)
    (hηE : ∀ d, (η d)⁻¹ ≤ Real.exp E) (A T : ℝ≥0)
    (hAP : (A : ℝ) ≤ Real.exp P) (hTP : (T : ℝ) ≤ Real.exp P) :
    jointBooleanWeightBudget (B := B) (O := O) (α := α) h C A T
      (fun d _ => scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d/2))
      (fun d => canonicalCubeMinorThreshold Unit (O d) α (h d) (c₀ d) (η d)) ≤
      Real.exp (jointBooleanWeightLog (B := B) (O := O) (α := α) h P E) := by
  change (∑ d, booleanAxisWeightCost (B d) (O d) α (h d) (C d) A T (c₀ d) (η d)) ≤
    Real.exp ((Fintype.card D : ℝ)+∑ d, booleanAxisWeightLog (B d) (O d) α (h d) P E)
  exact sum_le_exp_card_add_sum
    (fun d => booleanAxisWeightCost (B d) (O d) α (h d) (C d) A T (c₀ d) (η d))
    (fun d => booleanAxisWeightLog (B d) (O d) α (h d) P E)
    (fun d => booleanAxisWeightLog_nonneg (B d) (O d) α (h d) hP hE)
    (fun d => booleanAxisWeightCost_le_exp (B d) (O d) α (h d) (hh d)
      (hC d) (hc₀ d) (hη d) hP hE (hCP d) (hcP d) (hηE d) A T hAP hTP)

end Erdos3

end

section

namespace Erdos3

def booleanMinorLogEnvelope {A : Type*} [Semiring A] (d : ℕ) (t : A) : A :=
  (d : A) * d + d * t + 2 + d * d *
    (d * d * (d + 1 : A) ^ 2 + 3 * d + (d + 1) + d * (8 + (d + 1)) + 1 + t + 2)

def booleanInverseLogEnvelope {A : Type*} [Semiring A] (d : ℕ) (t : A) : A :=
  d + (d : A) ^ 2 + d * (t + d + d * d) + booleanMinorLogEnvelope d t

def booleanDerivativeLogEnvelope {A : Type*} [Semiring A] (d : ℕ) (t : A) : A :=
  t * d * (d + 1) + d + (t + 2 * d + (d : A) * d)

def booleanWeightLogEnvelope {A : Type*} [Semiring A] (d : ℕ) (t : A) : A :=
  (t + 3 * d + 1 + ((d + 1 : A) ^ 2 + 2 * d + 2) + 2 * (t * d) + t + 1) +
    (t * d * (d + 1) + t + booleanMinorLogEnvelope d t +
      (t * d * (d + 1) + (d : A) ^ 2 + d + (t + 2 * d + d * d) +
        d * (t + d + d * d + 1))) + 1

theorem booleanAxisLogEnvelopes_nonneg (d : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ booleanMinorLogEnvelope d t ∧ 0 ≤ booleanInverseLogEnvelope d t ∧
      0 ≤ booleanDerivativeLogEnvelope d t ∧ 0 ≤ booleanWeightLogEnvelope d t := by
  dsimp only [booleanMinorLogEnvelope, booleanInverseLogEnvelope,
    booleanDerivativeLogEnvelope, booleanWeightLogEnvelope]
  exact ⟨by positivity, by positivity, by positivity, by positivity⟩

theorem canonicalBooleanMinorLog_le_envelope (O α : Type*) [Fintype O] [Fintype α]
    (d h : ℕ) (hO : Fintype.card O ≤ d) (hα : Fintype.card α ≤ d) (hh : h ≤ d)
    (hN : cubeMinorVariableCount O α h ≤ d) (hdegree : cubeMinorDegree O h ≤ d)
    {P E t : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) (hPt : P ≤ t) (hEt : E ≤ t) :
    canonicalBooleanMinorLog O α h P E ≤ booleanMinorLogEnvelope d t := by
  have ht := hP.trans hPt
  have hOr : (Fintype.card O : ℝ) ≤ d := Nat.cast_le.mpr hO
  have hαr : (Fintype.card α : ℝ) ≤ d := Nat.cast_le.mpr hα
  have hhr : (h : ℝ) ≤ d := Nat.cast_le.mpr hh
  have hNr : (cubeMinorVariableCount O α h : ℝ) ≤ d := Nat.cast_le.mpr hN
  have hdr : (cubeMinorDegree O h : ℝ) ≤ d := Nat.cast_le.mpr hdegree
  simp only [canonicalBooleanMinorLog, cubeMinorThresholdLog, cubeMinorScaleLog,
    cubeMinorConstantLog, booleanMinorLogEnvelope, Nat.cast_mul, Nat.cast_one]
  gcongr

theorem booleanAxisLogs_le_envelopes (B O α : Type*) [Fintype B] [Fintype O] [Fintype α]
    (d h : ℕ) (hO : Fintype.card O ≤ d) (hα : Fintype.card α ≤ d) (hh : h ≤ d)
    (hN : cubeMinorVariableCount O α h ≤ d) (hdegree : cubeMinorDegree O h ≤ d)
    {P E t : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) (hPt : P ≤ t) (hEt : E ≤ t)
    (hB : (Fintype.card B : ℝ) ≤ t) :
    productMinorInverseLog (Fintype.card O) (Fintype.card α) h P
        (canonicalBooleanMinorLog O α h P E) ≤ booleanInverseLogEnvelope d t ∧
      productMinorDerivativeLog (Fintype.card (BlockParameter B (Fin h) α))
        (Fintype.card O) (Fintype.card α) h P ≤ booleanDerivativeLogEnvelope d t ∧
      booleanAxisWeightLog B O α h P E ≤ booleanWeightLogEnvelope d t := by
  have ht := hP.trans hPt
  have hOr : (Fintype.card O : ℝ) ≤ d := Nat.cast_le.mpr hO
  have hαr : (Fintype.card α : ℝ) ≤ d := Nat.cast_le.mpr hα
  have hhr : (h : ℝ) ≤ d := Nat.cast_le.mpr hh
  have hsub : ((Fintype.card O - 1 : ℕ) : ℝ) ≤ d := Nat.cast_le.mpr ((Nat.sub_le _ _).trans hO)
  have hminor := canonicalBooleanMinorLog_le_envelope O α d h hO hα hh hN hdegree hP hE hPt hEt
  have hprod : (Fintype.card (B × Fin h) : ℝ) ≤ t * d := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] using
      mul_le_mul hB hhr (Nat.cast_nonneg h) ht
  have hblock : (Fintype.card (BlockParameter B (Fin h) α) : ℝ) ≤ t * d * (d + 1) := by
    simp only [BlockParameter, Fintype.card_prod, Fintype.card_fin, Fintype.card_option,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ t * ((d : ℝ) * (d + 1)) := by gcongr
      _ = _ := by ring
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [productMinorInverseLog, productMinorEntryLog, booleanInverseLogEnvelope]
    gcongr
  · dsimp only [productMinorDerivativeLog, productMinorPartialLog, booleanDerivativeLogEnvelope]
    gcongr
  · dsimp only [booleanAxisWeightLog, scalarCubeDerivativeLog, scalarCubeBoundaryLog,
      productMinorDeterminantLog, productMinorPartialLog, productMinorEntryLog, booleanWeightLogEnvelope]
    gcongr

end Erdos3

end

end OAI
