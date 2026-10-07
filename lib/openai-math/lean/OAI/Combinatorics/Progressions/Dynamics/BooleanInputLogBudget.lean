import OAI.Combinatorics.Progressions.Estimates.BooleanAxisLogEnvelope
import OAI.Combinatorics.Progressions.Estimates.DivergenceExponentialBounds
import OAI.Combinatorics.Progressions.Polynomial.BooleanPolynomialLogBudget

namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {D α : Type*} [Fintype D] [Fintype α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

noncomputable def jointBooleanTranslationLog (h : D → ℕ) (P E : ℝ) : ℝ :=
  Fintype.card (Σ d, O d)+Fintype.card (JointBlockParameter B h α)+
    3*jointBooleanInverseLog (O := O) (α := α) h P E+
    jointBooleanDerivativeLog (B := B) (O := O) (α := α) h P+
    jointBooleanWeightLog (B := B) (O := O) (α := α) h P E+1

noncomputable def jointBooleanPerturbationLog (h : D → ℕ) (P E : ℝ) : ℝ :=
  Fintype.card (JointBlockParameter B h α)+
    3*jointBooleanInverseLog (O := O) (α := α) h P E+
    jointBooleanDerivativeLog (B := B) (O := O) (α := α) h P+
    jointBooleanWeightLog (B := B) (O := O) (α := α) h P E+6

theorem jointBooleanTranslationLog_nonneg (h : D → ℕ) {P E : ℝ}
    (hP : 0 ≤ P) (hE : 0 ≤ E) :
    0 ≤ jointBooleanTranslationLog (B := B) (O := O) (α := α) h P E := by
  have := jointBooleanInverseLog_nonneg (O := O) (α := α) h hP hE
  have := jointBooleanDerivativeLog_nonneg (B := B) (O := O) (α := α) h hP
  have := jointBooleanWeightLog_nonneg (B := B) (O := O) (α := α) h hP hE
  unfold jointBooleanTranslationLog
  positivity

theorem jointBooleanPerturbationLog_nonneg (h : D → ℕ) {P E : ℝ}
    (hP : 0 ≤ P) (hE : 0 ≤ E) :
    0 ≤ jointBooleanPerturbationLog (B := B) (O := O) (α := α) h P E := by
  have := jointBooleanInverseLog_nonneg (O := O) (α := α) h hP hE
  have := jointBooleanDerivativeLog_nonneg (B := B) (O := O) (α := α) h hP
  have := jointBooleanWeightLog_nonneg (B := B) (O := O) (α := α) h hP hE
  unfold jointBooleanPerturbationLog
  positivity

variable [DecidableEq α] [∀ d, Nonempty (O d)]

theorem jointBooleanRegularizationBudget_le_exp (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (c₀ C η : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (hη : ∀ d, 0 < η d) {P E : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hcP : ∀ d, (c₀ d)⁻¹ ≤ Real.exp P) (hCP : ∀ d, C d ≤ Real.exp P)
    (hηE : ∀ d, (η d)⁻¹ ≤ Real.exp E) (A T : ℝ≥0)
    (hAP : (A : ℝ) ≤ Real.exp P) (hTP : (T : ℝ) ≤ Real.exp P) :
    (jointBooleanRegularizationBudget (B := B) (O := O) (α := α) h c₀ C A T η : ℝ) ≤
      Real.exp (jointBooleanTranslationLog (B := B) (O := O) (α := α) h P E) := by
  have hK := jointBooleanInverseBudget_canonical_le_exp (O := O) (α := α)
    h hh c₀ C η hc₀ hC hη hP hE hcP hCP hηE
  have hH := jointBooleanDerivativeBudget_le_exp (B := B) (O := O) (α := α) h C hC hP hCP
  have hS := jointBooleanWeightBudget_canonical_le_exp (B := B) (O := O) (α := α)
    h hh c₀ C η hc₀ hC hη hP hE hcP hCP hηE A T hAP hTP
  have hS0 := jointBooleanWeightBudget_nonneg (B := B) (O := O) (α := α) h C hC A T
    (fun d _ => scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d/2))
    (fun d _ => (scalarCubeProductBoundaryRadius_pos (B d × Fin (h d)) α (half_pos (hη d))).le)
    (fun d => canonicalCubeMinorThreshold Unit (O d) α (h d) (c₀ d) (η d))
    (fun d => (canonicalCubeMinorThreshold_pos Unit (O d) α (hh d) (hc₀ d) (hη d)).le)
  unfold jointBooleanRegularizationBudget jointBooleanTranslationBudget
  apply coe_toNNReal_le_exp
  exact translationDivergence_le_exp _ _ (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) hS0
    (jointBooleanInverseLog_nonneg (O := O) (α := α) h hP hE)
    (jointBooleanDerivativeLog_nonneg (B := B) (O := O) (α := α) h hP)
    (jointBooleanWeightLog_nonneg (B := B) (O := O) (α := α) h hP hE) hK hH hS

theorem booleanToleranceDivergence_le_exp (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    {ε P E : ℝ} (hε : 0 < ε) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hcP : ∀ d, (c₀ d)⁻¹ ≤ Real.exp P) (hCP : ∀ d, C d ≤ Real.exp P)
    (hηE : ((ε/4)/((Fintype.card D : ℝ)+1))⁻¹ ≤ Real.exp E) (A T : ℝ≥0)
    (hAP : (A : ℝ) ≤ Real.exp P) (hTP : (T : ℝ) ≤ Real.exp P) :
    booleanToleranceDivergence (B := B) (O := O) (α := α) h c₀ C A T ε ≤
      Real.exp (jointBooleanPerturbationLog (B := B) (O := O) (α := α) h P E) := by
  let η : D → ℝ := fun _ => (ε/4)/((Fintype.card D : ℝ)+1)
  have hη : ∀ d, 0 < η d := by intro d; dsimp [η]; positivity
  have hK := jointBooleanInverseBudget_canonical_le_exp (O := O) (α := α)
    h hh c₀ C η hc₀ hC hη hP hE hcP hCP (fun _ => hηE)
  have hH := jointBooleanDerivativeBudget_le_exp (B := B) (O := O) (α := α) h C hC hP hCP
  have hS := jointBooleanWeightBudget_canonical_le_exp (B := B) (O := O) (α := α)
    h hh c₀ C η hc₀ hC hη hP hE hcP hCP (fun _ => hηE) A T hAP hTP
  have hS0 := jointBooleanWeightBudget_nonneg (B := B) (O := O) (α := α) h C hC A T
    (booleanToleranceBoundary (B := B) (α := α) h ε)
    (fun d i => (booleanToleranceBoundary_pos h hε d i).le)
    (booleanToleranceMinor (O := O) (α := α) h c₀ ε)
    (fun d => (booleanToleranceMinor_pos h hh c₀ hc₀ hε d).le)
  exact perturbationDivergence_le_exp _ (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) hS0
    (jointBooleanInverseLog_nonneg (O := O) (α := α) h hP hE)
    (jointBooleanDerivativeLog_nonneg (B := B) (O := O) (α := α) h hP)
    (jointBooleanWeightLog_nonneg (B := B) (O := O) (α := α) h hP hE) hK hH hS

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem dividedAccuracy_inverse_le_exp (d : ℕ) {ε E : ℝ}
    (hε : 0 < ε) (hεE : ε⁻¹ ≤ Real.exp E) :
    (ε/(8*((d : ℝ)+1)))⁻¹ ≤ Real.exp (E+d+3) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h8 : (8 : ℝ) ≤ Real.exp 3 := by
    calc
      _ = (2 : ℝ)^3 := by norm_num
      _ ≤ (Real.exp 1)^3 := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hd : (d : ℝ)+1 ≤ Real.exp d := Real.add_one_le_exp _
  rw [inv_div, div_eq_mul_inv]
  calc
    _ ≤ (Real.exp 3*Real.exp d)*Real.exp E := by gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

variable {D α : Type*} [Fintype D] [Fintype α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

noncomputable def affineComparisonInputLog (Z : Type*) [Fintype Z]
    (h : D → ℕ) (degree : ℕ) (P E : ℝ) : ℝ :=
  let E' := E+Fintype.card D+3
  jointBooleanTranslationLog (B := B) (O := O) (α := α) h P E'+
    jointBooleanPerturbationLog (B := B) (O := O) (α := α) h P E'+
    booleanToleranceC2Log (B := B) (α := α) Z h degree P+
    jointBooleanInverseLog (O := O) (α := α) h P E'+Fintype.card (Σ d, O d)+E+3

theorem affineComparisonInputLog_nonneg (Z : Type*) [Fintype Z]
    (h : D → ℕ) (degree : ℕ) {P E : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) :
    0 ≤ affineComparisonInputLog (B := B) (O := O) (α := α) Z h degree P E := by
  have hE' : 0 ≤ E+Fintype.card D+3 := by positivity
  have := jointBooleanTranslationLog_nonneg (B := B) (O := O) (α := α) h hP hE'
  have := jointBooleanPerturbationLog_nonneg (B := B) (O := O) (α := α) h hP hE'
  have := booleanToleranceC2Log_nonneg (B := B) (α := α) Z h degree hP
  have := jointBooleanInverseLog_nonneg (O := O) (α := α) h hP hE'
  unfold affineComparisonInputLog
  positivity

theorem affineComparisonInputLog_bounds [DecidableEq α] [∀ d, Nonempty (O d)]
    (Z : Type*) [Fintype Z] (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (A T : ℝ≥0) (degree : ℕ) {Csum Wsum ε P E : ℝ}
    (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum) (hε : 0 < ε) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hcP : ∀ d, (c₀ d)⁻¹ ≤ Real.exp P) (hCP : ∀ d, C d ≤ Real.exp P)
    (hAP : (A : ℝ) ≤ Real.exp P) (hTP : (T : ℝ) ≤ Real.exp P)
    (hCsumP : Csum ≤ Real.exp P) (hWsumP : Wsum ≤ Real.exp P) (hεE : ε⁻¹ ≤ Real.exp E) :
    let P' := affineComparisonInputLog (B := B) (O := O) (α := α) Z h degree P E
    (jointBooleanRegularizationBudget (B := B) (O := O) (α := α) h c₀ C A T
      (fun _ => (ε/2)/(4*((Fintype.card D : ℝ)+1))) : ℝ) ≤ Real.exp P' ∧
    (Fintype.card (Σ d, O d) : ℝ) ≤ Real.exp P' ∧
    (jointBooleanInverseBudget (O := O) (α := α) h C
      (booleanToleranceMinor (O := O) (α := α) h c₀ (ε/2)) : ℝ) ≤ Real.exp P' ∧
    booleanToleranceC2 (B := B) (α := α) Z h degree Csum Wsum ≤ Real.exp P' ∧
    booleanToleranceDivergence (B := B) (O := O) (α := α) h c₀ C A T (ε/2) ≤ Real.exp P' ∧
    (ε/4)⁻¹ ≤ Real.exp P' := by
  let E' := E+Fintype.card D+3
  have hE' : 0 ≤ E' := by dsimp [E']; positivity
  have hL0 := jointBooleanTranslationLog_nonneg (B := B) (O := O) (α := α) h hP hE'
  have hQ0 := jointBooleanPerturbationLog_nonneg (B := B) (O := O) (α := α) h hP hE'
  have hM0 := booleanToleranceC2Log_nonneg (B := B) (α := α) Z h degree hP
  have hK0 := jointBooleanInverseLog_nonneg (O := O) (α := α) h hP hE'
  have hη : 0 < (ε/2)/(4*((Fintype.card D : ℝ)+1)) := by positivity
  have hηE : ((ε/2)/(4*((Fintype.card D : ℝ)+1)))⁻¹ ≤ Real.exp E' := by
    have heq : (ε/2)/(4*((Fintype.card D : ℝ)+1)) = ε/(8*((Fintype.card D : ℝ)+1)) := by
      simp only [div_mul_eq_div_div]; ring
    rw [heq]
    exact dividedAccuracy_inverse_le_exp _ hε hεE
  have hsplit : (ε/2)/4/((Fintype.card D : ℝ)+1) = (ε/2)/(4*((Fintype.card D : ℝ)+1)) := by
    rw [div_mul_eq_div_div]
  have htailE : ((ε/2)/4/((Fintype.card D : ℝ)+1))⁻¹ ≤ Real.exp E' := by rwa [hsplit]
  have hL := jointBooleanRegularizationBudget_le_exp (B := B) (O := O) (α := α)
    h hh c₀ C (fun _ => (ε/2)/(4*((Fintype.card D : ℝ)+1))) hc₀ hC (fun _ => hη)
    hP hE' hcP hCP (fun _ => hηE) A T hAP hTP
  have hK := jointBooleanInverseBudget_canonical_le_exp (O := O) (α := α)
    h hh c₀ C (fun _ => (ε/2)/4/((Fintype.card D : ℝ)+1)) hc₀ hC
    (fun _ => by rw [hsplit]; exact hη) hP hE' hcP hCP (fun _ => htailE)
  have hM := booleanToleranceC2_le_exp (B := B) (α := α) Z h degree hCsum hWsum hP hCsumP hWsumP
  have hQ := booleanToleranceDivergence_le_exp (B := B) (O := O) (α := α)
    h hh c₀ C hc₀ hC (half_pos hε) hP hE' hcP hCP htailE A T hAP hTP
  have hm : (Fintype.card (Σ d, O d) : ℝ) ≤ Real.exp (Fintype.card (Σ d, O d) : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card (Σ d, O d) : ℝ)]
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ = (2 : ℝ)^2 := by norm_num
      _ ≤ (Real.exp 1)^2 := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have ha : (ε/4)⁻¹ ≤ Real.exp (E+2) := by
    rw [inv_div, div_eq_mul_inv]
    calc
      _ ≤ Real.exp 2*Real.exp E := by gcongr
      _ = _ := by rw [← Real.exp_add, add_comm]
  dsimp only
  refine ⟨hL.trans ?_, hm.trans ?_, hK.trans ?_, hM.trans ?_, hQ.trans ?_, ha.trans ?_⟩ <;>
    apply Real.exp_le_exp.mpr <;> unfold affineComparisonInputLog <;> change _ ≤
      jointBooleanTranslationLog (B := B) (O := O) (α := α) h P E'+
        jointBooleanPerturbationLog (B := B) (O := O) (α := α) h P E'+
        booleanToleranceC2Log (B := B) (α := α) Z h degree P+
        jointBooleanInverseLog (O := O) (α := α) h P E'+Fintype.card (Σ d, O d)+E+3 <;>
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (Σ d, O d))]

end Erdos3

end

end OAI
