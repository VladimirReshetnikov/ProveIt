import OAI.Combinatorics.Progressions.Sampling.SamplerParameterLog

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {D : Type*} [Fintype D] {B : D → Type*} [∀ d, Fintype (B d)]

noncomputable def unitProfileCoefficientLog (A T : ℝ≥0) : ℝ :=
  (∑ d, (Fintype.card (B d) : ℝ)) + A + T + 7

theorem unitProfileCoefficientLog_nonneg (A T : ℝ≥0) :
    0 ≤ unitProfileCoefficientLog (B := B) A T := by
  unfold unitProfileCoefficientLog
  positivity

theorem unitProfileCoefficientLog_bounds (A T : ℝ≥0) :
    let P := unitProfileCoefficientLog (B := B) A T
    (∀ d, (unitProfilePrincipalSize (B := B) d)⁻¹ ≤ Real.exp P) ∧
    (∀ d, 2 * unitProfilePrincipalSize (B := B) d ≤ Real.exp P) ∧
    (A : ℝ) ≤ Real.exp P ∧ (T : ℝ) ≤ Real.exp P := by
  classical
  let P := unitProfileCoefficientLog (B := B) A T
  have hP : 0 ≤ P := unitProfileCoefficientLog_nonneg A T
  have hsum : 0 ≤ ∑ d, (Fintype.card (B d) : ℝ) := by positivity
  have hB (d : D) : (Fintype.card (B d) : ℝ) ≤ ∑ e, (Fintype.card (B e) : ℝ) :=
    Finset.single_le_sum (f := fun e => (Fintype.card (B e) : ℝ))
      (fun e _ => Nat.cast_nonneg _) (Finset.mem_univ d)
  have hPE : P ≤ Real.exp P := by linarith [Real.add_one_le_exp P]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d
    change (1 / (8 * ((Fintype.card (B d) : ℝ) + 1)))⁻¹ ≤ Real.exp P
    rw [one_div, inv_inv]
    calc
      _ ≤ Real.exp 7 * Real.exp (Fintype.card (B d)) := by
        gcongr
        · linarith [Real.add_one_le_exp (7 : ℝ)]
        · exact Real.add_one_le_exp _
      _ = Real.exp (7 + (Fintype.card (B d) : ℝ)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp P := by
        apply Real.exp_le_exp.mpr
        dsimp [P, unitProfileCoefficientLog]
        linarith [hB d, A.coe_nonneg, T.coe_nonneg]
  · intro d
    apply le_trans (b := 1) _ (Real.one_le_exp hP)
    change 2 * (1 / (8 * ((Fintype.card (B d) : ℝ) + 1))) ≤ 1
    rw [← mul_div_assoc, mul_one]
    apply (div_le_one (by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (B d))]
  · apply le_trans (b := P) _ hPE
    dsimp [P, unitProfileCoefficientLog]
    linarith [T.coe_nonneg]
  · apply le_trans (b := P) _ hPE
    dsimp [P, unitProfileCoefficientLog]
    linarith [A.coe_nonneg]

theorem uniformProfileScale_inverse_le_exp
    (G Z α : Type*) [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
    {O : D → Type*} [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (A T : ℝ≥0) (degree : ℕ)
    {ε E : ℝ} (hε : 0 < ε) (hE : 0 ≤ E) (hεE : ε⁻¹ ≤ Real.exp E) :
    (booleanMassPerturbationScale (B := B) (O := O) (α := α)
      (Z ⊕ (Σ d, SamplerCoefficientSlot G B h d)) h
      (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
      A T degree 1 ε)⁻¹ ≤
      Real.exp (6 * booleanMassInputLog (B := B) (O := O) (α := α) h degree
        (unitProfileCoefficientLog (B := B) A T) E (samplerParameterLog G Z α (B := B) h) + 8) := by
  obtain ⟨hcP, hCP, hAP, hTP⟩ := unitProfileCoefficientLog_bounds (B := B) A T
  have hP := unitProfileCoefficientLog_nonneg (B := B) A T
  exact booleanMassPerturbationScale_input_le_exp _ h hh
    (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
    (unitProfilePrincipalSize_pos (B := B))
    (fun d => mul_nonneg (by norm_num) (unitProfilePrincipalSize_pos (B := B) d).le)
    A T degree zero_le_one hε hP hE (samplerParameterLog_nonneg G Z α h)
    hcP hCP hAP hTP (Real.one_le_exp hP) hεE (samplerParameter_card_le_exp G Z α h)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {D α : Type*} [Fintype D] [Fintype α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

noncomputable def booleanRegularizationInputLog (h : D → ℕ) (P E : ℝ) : ℝ :=
  jointBooleanTranslationLog (B := B) (O := O) (α := α) h P (E + Fintype.card D + 3) + E + 3

theorem booleanRegularizationInputLog_nonneg (h : D → ℕ) {P E : ℝ}
    (hP : 0 ≤ P) (hE : 0 ≤ E) :
    0 ≤ booleanRegularizationInputLog (B := B) (O := O) (α := α) h P E := by
  have hL := jointBooleanTranslationLog_nonneg (B := B) (O := O) (α := α)
    h hP (show 0 ≤ E + Fintype.card D + 3 by positivity)
  unfold booleanRegularizationInputLog
  positivity

theorem booleanRegularizationRadius_input_le_exp [DecidableEq α] [∀ d, Nonempty (O d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (c₀ C : D → ℝ)
    (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d) (A T : ℝ≥0)
    {ε P E : ℝ} (hε : 0 < ε) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hcP : ∀ d, (c₀ d)⁻¹ ≤ Real.exp P) (hCP : ∀ d, C d ≤ Real.exp P)
    (hAP : (A : ℝ) ≤ Real.exp P) (hTP : (T : ℝ) ≤ Real.exp P)
    (hεE : ε⁻¹ ≤ Real.exp E) :
    (booleanRegularizationRadius (B := B) (O := O) (α := α) h c₀ C A T ε)⁻¹ ≤
      Real.exp (2 * booleanRegularizationInputLog (B := B) (O := O) (α := α) h P E + 2) := by
  let E' := E + Fintype.card D + 3
  have hE' : 0 ≤ E' := by dsimp [E']; positivity
  have hηE : (ε / (4 * ((Fintype.card D : ℝ) + 1)))⁻¹ ≤ Real.exp E' := by
    rw [div_mul_eq_div_div, inv_div, div_div_eq_mul_div, div_eq_mul_inv]
    calc
      _ ≤ (Real.exp (Fintype.card D) * Real.exp 3) * Real.exp E := by
        gcongr
        · exact Real.add_one_le_exp _
        · linarith [Real.add_one_le_exp (3 : ℝ)]
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; dsimp [E']; ring
  have hη : ∀ _d : D, 0 < ε / (4 * ((Fintype.card D : ℝ) + 1)) := by
    intro d
    positivity
  have hL := jointBooleanRegularizationBudget_le_exp (B := B) (O := O) (α := α)
    h hh c₀ C (fun _ => ε / (4 * ((Fintype.card D : ℝ) + 1))) hc₀ hC hη hP hE'
    hcP hCP (fun _ => hηE) A T hAP hTP
  have hL0 := jointBooleanTranslationLog_nonneg (B := B) (O := O) (α := α) h hP hE'
  apply booleanRegularizationRadius_inverse_le_exp h c₀ C A T hε
    (booleanRegularizationInputLog_nonneg h hP hE)
  · apply hL.trans
    apply Real.exp_le_exp.mpr
    change _ ≤ jointBooleanTranslationLog (B := B) (O := O) (α := α) h P E' + E + 3
    linarith
  · apply hεE.trans
    apply Real.exp_le_exp.mpr
    change _ ≤ jointBooleanTranslationLog (B := B) (O := O) (α := α) h P E' + E + 3
    linarith

theorem uniformProfileRadius_inverse_le_exp [DecidableEq α] [∀ d, Nonempty (O d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (A T : ℝ≥0)
    {ε E : ℝ} (hε : 0 < ε) (hE : 0 ≤ E) (hεE : ε⁻¹ ≤ Real.exp E) :
    (booleanRegularizationRadius (B := B) (O := O) (α := α) h
      (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d) A T ε)⁻¹ ≤
      Real.exp (2 * booleanRegularizationInputLog (B := B) (O := O) (α := α) h
        (unitProfileCoefficientLog (B := B) A T) E + 2) := by
  obtain ⟨hcP, hCP, hAP, hTP⟩ := unitProfileCoefficientLog_bounds (B := B) A T
  exact booleanRegularizationRadius_input_le_exp h hh
    (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
    (unitProfilePrincipalSize_pos (B := B))
    (fun d => mul_nonneg (by norm_num) (unitProfilePrincipalSize_pos (B := B) d).le)
    A T hε (unitProfileCoefficientLog_nonneg (B := B) A T) hE hcP hCP hAP hTP hεE

end Erdos3

end

end OAI
