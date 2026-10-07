import OAI.Combinatorics.Progressions.Estimates.NativeWeightPairRemoval

namespace OAI

section

namespace Erdos3.NativeMixedReductionData

open scoped BigOperators

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

def translationCodeEquiv (k : Fin 4 → Fin V.outputDim) :
    D.TranslationCode k ≃
      (Σ a₂ : MixedExpansionIndex V, Σ a₄ : MixedExpansionIndex V,
        Fin (D.translation.selectedExpansion (k 1) a₂).count ×
          Fin (D.translation.selectedExpansion (k 3) a₄).count) where
  toFun t := ⟨t.second, t.fourth, t.secondTerm, t.fourthTerm⟩
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance translationCodeFintype (k : Fin 4 → Fin V.outputDim) :
    Fintype (D.TranslationCode k) :=
  Fintype.ofEquiv _ (D.translationCodeEquiv k).symm

def reductionCodeEquiv (k : Fin 4 → Fin V.outputDim) :
    D.ReductionCode k ≃ (Σ t : D.TranslationCode k,
      Fin (D.parallelogram (D.translationCoordinates k t)).count) where
  toFun a := ⟨a.translations, a.term⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance reductionCodeFintype (k : Fin 4 → Fin V.outputDim) :
    Fintype (D.ReductionCode k) :=
  Fintype.ofEquiv _ (D.reductionCodeEquiv k).symm

theorem translationCode_card (k : Fin 4 → Fin V.outputDim) :
    (Fintype.card (D.TranslationCode k) : ℝ) ≤ Real.exp (4 * P) := by
  classical
  have he := D.translation.right_dimension
  calc
    (Fintype.card (D.TranslationCode k) : ℝ) =
        ∑ a₂ : MixedExpansionIndex V, ∑ a₄ : MixedExpansionIndex V,
          ((D.translation.selectedExpansion (k 1) a₂).count : ℝ) *
            ((D.translation.selectedExpansion (k 3) a₄).count : ℝ) := by
      rw [Fintype.card_congr (D.translationCodeEquiv k)]
      simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
        Nat.cast_sum, Nat.cast_mul]
    _ ≤ ∑ _ : MixedExpansionIndex V, ∑ _ : MixedExpansionIndex V,
        Real.exp P * Real.exp P := by
      apply Finset.sum_le_sum
      intro a₂ _
      apply Finset.sum_le_sum
      intro a₄ _
      exact mul_le_mul (D.translation.selectedExpansion (k 1) a₂).count_bound
        (D.translation.selectedExpansion (k 3) a₄).count_bound
        (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = (Fintype.card (MixedExpansionIndex V) : ℝ) *
        ((Fintype.card (MixedExpansionIndex V) : ℝ) * (Real.exp P * Real.exp P)) := by
      simp
    _ ≤ Real.exp P * (Real.exp P * (Real.exp P * Real.exp P)) := by
      gcongr
    _ = Real.exp (4 * P) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

theorem reductionCode_card (k : Fin 4 → Fin V.outputDim) :
    (Fintype.card (D.ReductionCode k) : ℝ) ≤ Real.exp (5 * P) := by
  classical
  calc
    (Fintype.card (D.ReductionCode k) : ℝ) =
        ∑ t : D.TranslationCode k, ((D.parallelogram (D.translationCoordinates k t)).count : ℝ) := by
      rw [Fintype.card_congr (D.reductionCodeEquiv k)]
      simp only [Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
    _ ≤ ∑ _ : D.TranslationCode k, Real.exp P := by
      exact Finset.sum_le_sum (fun t _ => (D.parallelogram (D.translationCoordinates k t)).count_bound)
    _ = (Fintype.card (D.TranslationCode k) : ℝ) * Real.exp P := by simp
    _ ≤ Real.exp (4 * P) * Real.exp P :=
      mul_le_mul_of_nonneg_right (D.translationCode_card k) (Real.exp_nonneg P)
    _ = Real.exp (5 * P) := by
      rw [← Real.exp_add]
      congr 1
      ring

end Erdos3.NativeMixedReductionData

end

section

namespace Erdos3.NativeMixedReductionData

open scoped BigOperators

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

theorem double_translation (h₁ h₂ h₃ h₄ δ : ℤ)
    (hrel : -h₁ + h₂ + h₃ - h₄ = 0) {X : Type*} (S : Finset X) (n : X → ℤ)
    (k : Fin 4 → Fin V.outputDim) (f : X → ℂ) (q : ℝ)
    (hcorr : Real.exp (-q) ≤
      ‖𝔼 u ∈ S, f u * translatedMixedProduct V k h₁ h₂ h₃ h₄ δ (n u)‖) :
    ∃ (t : D.TranslationCode k) (c : D.LowerCode t h₂ h₄ δ),
      Real.exp (-(q + 6 * P)) ≤ ‖𝔼 u ∈ S,
        f u * D.translationGlobal k t ![h₁, h₂, h₃, n u, δ] *
          D.translationLower t h₂ h₄ δ c (n u) *
          untranslatedMixedProduct V (D.translationCoordinates k t) h₁ h₂ h₃ h₄ (n u)‖ := by
  let f₄ (u : X) := f u * star (V.eval (k 0) (fun j => correlationInput h₁ (n u) j.1)) *
    V.eval (k 1) (fun j => correlationInput h₂ (n u + δ) j.1) *
    V.eval (k 2) (fun j => correlationInput h₃ (n u) j.1)
  have hc₄ : Real.exp (-q) ≤ ‖𝔼 u ∈ S, f₄ u *
      star (V.eval (k 3) (fun j => correlationInput h₄ (n u + δ) j.1))‖ := by
    simpa only [f₄, translatedMixedProduct, fourPointProduct, mul_assoc] using hcorr
  obtain ⟨a₄, b₄, c₄, h₄'⟩ := D.translation_negative h₄ δ S n (k 3) f₄ q hc₄
  let f₂ (u : X) := f u * star (V.eval (k 0) (fun j => correlationInput h₁ (n u) j.1)) *
    V.eval (k 2) (fun j => correlationInput h₃ (n u) j.1) *
    star (D.correction h₄ δ (k 3) a₄ b₄ c₄ (n u))
  have hc₂ : Real.exp (-(q + 3 * P)) ≤ ‖𝔼 u ∈ S, f₂ u *
      V.eval (k 1) (fun j => correlationInput h₂ (n u + δ) j.1)‖ := by
    simpa only [f₄, f₂, mul_assoc, mul_left_comm, mul_comm] using h₄'
  obtain ⟨a₂, b₂, c₂, h₂'⟩ := D.translation_positive h₂ δ S n (k 1) f₂ (q + 3 * P) hc₂
  let t : D.TranslationCode k := ⟨a₂, a₄, b₂, b₄⟩
  let c : D.LowerCode t h₂ h₄ δ := ⟨c₂, c₄⟩
  refine ⟨t, c, ?_⟩
  rw [show (q + 3 * P) + 3 * P = q + 6 * P by ring] at h₂'
  have hmean : (𝔼 u ∈ S, f₂ u * D.correction h₂ δ (k 1) a₂ b₂ c₂ (n u)) =
      𝔼 u ∈ S, f u * D.translationGlobal k t ![h₁, h₂, h₃, n u, δ] *
        D.translationLower t h₂ h₄ δ c (n u) *
        untranslatedMixedProduct V (D.translationCoordinates k t) h₁ h₂ h₃ h₄ (n u) := by
    apply Finset.expect_congr rfl
    intro u _
    exact D.correction_factorization k t h₁ h₂ h₃ h₄ δ (n u) c (f u) hrel
  rwa [← hmean]

end Erdos3.NativeMixedReductionData

end

section

namespace Erdos3.NativeMixedReductionData

open scoped BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

theorem reduce_quadruple (h₁ h₂ h₃ h₄ δ : ℤ)
    (hrel : -h₁ + h₂ + h₃ - h₄ = 0) {X : Type*} (S : Finset X) (n : X → ℤ)
    (k : Fin 4 → Fin V.outputDim) (f : X → ℂ) (q : ℝ)
    (hcorr : Real.exp (-q) ≤
      ‖𝔼 u ∈ S, f u * translatedMixedProduct V k h₁ h₂ h₃ h₄ δ (n u)‖) :
    ∃ (a : D.ReductionCode k) (c : D.LowerCode a.translations h₂ h₄ δ),
      Real.exp (-(q + 7 * P)) ≤ ‖𝔼 u ∈ S,
        f u * D.globalError k a ![h₁, h₂, h₃, n u, δ] *
          D.translationLower a.translations h₂ h₄ δ c (n u)‖ := by
  obtain ⟨t, c, ht⟩ := D.double_translation h₁ h₂ h₃ h₄ δ hrel S n k f q hcorr
  let g (u : X) := f u * D.translationGlobal k t ![h₁, h₂, h₃, n u, δ] *
    D.translationLower t h₂ h₄ δ c (n u)
  have hg : Real.exp (-(q + 6 * P)) ≤ ‖𝔼 u ∈ S, g u *
      mixedParallelogramProduct V (D.translationCoordinates k t) ![h₁, h₂, h₃, n u]‖ := by
    simpa only [g, untranslatedMixedProduct_eq V (D.translationCoordinates k t)
      h₁ h₂ h₃ h₄ _ hrel] using ht
  obtain ⟨j, hj⟩ := (D.parallelogram (D.translationCoordinates k t)).select_sample_product_correlation
    S (fun u => ![h₁, h₂, h₃, n u]) g hg
  refine ⟨⟨t, j⟩, c, ?_⟩
  rw [show (q + 6 * P) + P = q + 7 * P by ring] at hj
  have hglobal (u : X) : D.globalError k ⟨t, j⟩ ![h₁, h₂, h₃, n u, δ] =
      D.translationGlobal k t ![h₁, h₂, h₃, n u, δ] *
        ((D.parallelogram (D.translationCoordinates k t)).test j).eval ![h₁, h₂, h₃, n u] := rfl
  simpa only [hglobal, g, mul_assoc, mul_left_comm, mul_comm] using hj

end Erdos3.NativeMixedReductionData

end

section

namespace Erdos3.NativeMixedReductionData

open scoped BigOperators

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

theorem reduce_family {I X : Type*} (H : Finset I) (hH : H.Nonempty)
    (S : I → Finset X) (n : I → X → ℤ) (h₁ h₂ h₃ h₄ δ : I → ℤ)
    (k : Fin 4 → Fin V.outputDim) (f : I → X → ℂ) (q : ℝ)
    (hrel : ∀ i ∈ H, -h₁ i + h₂ i + h₃ i - h₄ i = 0)
    (hcorr : ∀ i ∈ H, Real.exp (-q) ≤
      ‖𝔼 u ∈ S i, f i u * translatedMixedProduct V k (h₁ i) (h₂ i) (h₃ i) (h₄ i) (δ i) (n i u)‖) :
    ∃ (a : D.ReductionCode k) (Q : Finset I), Q ⊆ H ∧ Q.Nonempty ∧
      Real.exp (-(5 * P)) * (H.card : ℝ) ≤ (Q.card : ℝ) ∧
      ∀ i ∈ Q, ∃ c : D.LowerCode a.translations (h₂ i) (h₄ i) (δ i),
        Real.exp (-(q + 7 * P)) ≤ ‖𝔼 u ∈ S i,
          f i u * D.globalError k a ![h₁ i, h₂ i, h₃ i, n i u, δ i] *
            D.translationLower a.translations (h₂ i) (h₄ i) (δ i) c (n i u)‖ := by
  let rel (i : I) (_ : Unit) (a : D.ReductionCode k) : Prop :=
    ∃ c : D.LowerCode a.translations (h₂ i) (h₄ i) (δ i),
      Real.exp (-(q + 7 * P)) ≤ ‖𝔼 u ∈ S i,
        f i u * D.globalError k a ![h₁ i, h₂ i, h₃ i, n i u, δ i] *
          D.translationLower a.translations (h₂ i) (h₄ i) (δ i) c (n i u)‖
  have hchoice : ∀ i ∈ H, ∀ b, ∃ a, rel i b a := by
    intro i hi _
    exact D.reduce_quadruple (h₁ i) (h₂ i) (h₃ i) (h₄ i) (δ i) (hrel i hi)
      (S i) (n i) k (f i) q (hcorr i hi)
  obtain ⟨a, Q, hsub, hQ, hsize, hfixed⟩ :=
    exists_large_fixed_choices H hH rel hchoice (D.reductionCode_card k)
  refine ⟨a (), Q, hsub, hQ, ?_, fun i hi => hfixed i hi ()⟩
  simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hsize

end Erdos3.NativeMixedReductionData

end

end OAI
