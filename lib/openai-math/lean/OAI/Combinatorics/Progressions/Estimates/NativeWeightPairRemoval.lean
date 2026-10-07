import OAI.Combinatorics.Progressions.Estimates.NativeLocalPivotVerticalPartners
import OAI.Combinatorics.Progressions.Geometry.MixedShiftCoordinate
import OAI.Combinatorics.Progressions.Geometry.NativeCoordinatePairs
import OAI.Combinatorics.Progressions.Geometry.SupportedCorrelationPairs
import OAI.Combinatorics.Progressions.Lattices.MixedTranslationAffineInput
import OAI.Combinatorics.Progressions.Lattices.NativeFrozenAffineExpansion

namespace OAI

section

namespace Erdos3.NativeIntegerExpansion

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem select_sample_product_correlation {σ X : Type*} {w : σ → ℕ} {s : ℕ} {p q : ℝ}
    {eta : (σ → ℤ) → ℂ} (E : NativeIntegerExpansion w s p eta)
    (S : Finset X) (sample : X → σ → ℤ) (f : X → ℂ)
    (hcorr : Real.exp (-q) ≤ ‖𝔼 u ∈ S, f u * eta (sample u)‖) :
    ∃ i : Fin E.count, Real.exp (-(q + p)) ≤
      ‖𝔼 u ∈ S, f u * (E.test i).eval (sample u)‖ := by
  have hpoint (u : X) : f u * eta (sample u) =
      ∑ i, E.coefficient i * (f u * (E.test i).eval (sample u)) := by
    rw [E.eval, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hmean : (𝔼 u ∈ S, f u * eta (sample u)) =
      ∑ i, E.coefficient i * (𝔼 u ∈ S, f u * (E.test i).eval (sample u)) := by
    calc
      _ = 𝔼 u ∈ S, ∑ i, E.coefficient i * (f u * (E.test i).eval (sample u)) :=
        Finset.expect_congr rfl (fun u _ => hpoint u)
      _ = _ := by simp_rw [Finset.expect_sum_comm, ← Finset.mul_expect]
  obtain ⟨i, hi⟩ := exists_large_weighted_term E.coefficient
    (fun i => 𝔼 u ∈ S, f u * (E.test i).eval (sample u))
    (Real.exp_pos (-q)) (Real.exp_pos p) E.cost (by rwa [← hmean])
  refine ⟨i, ?_⟩
  have heq : Real.exp (-q) / Real.exp p = Real.exp (-(q + p)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rwa [heq] at hi

end Erdos3.NativeIntegerExpansion

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_frozen_translation_expansion {σ : Type*} [Fintype σ] [DecidableEq σ]
    (bound : σ → ℕ) (l : List σ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p)
      (S : Finset σ) (A b : Option σ → ℤ) (a : BinaryTensorIndex (Fin W.outputDim) l.length),
      A none = 0 → (∀ i, i ∉ S → A (some i) = 0) →
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (∑ i ∈ S, bound i) ((p + C) ^ C)
        (fun x => coordinateTranslationExpansion W.eval l a (fun j => b j + A j * x ()))) := by
  induction l with
  | nil =>
    obtain ⟨C, hC, hfreeze⟩ := exists_frozen_affine_expansion bound
    refine ⟨C, hC, ?_⟩
    intro p W S A b a _ hA
    obtain ⟨E, _⟩ := hfreeze W S (fun i => A (some i)) (fun i => b (some i)) a hA
    exact ⟨E⟩
  | cons i l ih =>
    obtain ⟨a, _, hprevious⟩ := ih
    obtain ⟨c, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
    let X : Polynomial ℕ := Polynomial.X
    obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
      (((X + Polynomial.C a) ^ a + Polynomial.C c) ^ c)
    refine ⟨C, hC, ?_⟩
    intro p W S A b k hnone hA
    have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
    let q := (p + a) ^ a
    have hq : 0 ≤ q := by dsimp [q]; positivity
    let A' (j : Option σ) := A (coordinateReplaceIndex i j)
    let b' (j : Option σ) := b (coordinateReplaceIndex i j)
    have hnone' : A' none = 0 := by simp [A', coordinateReplaceIndex, hnone]
    have hA' (j : σ) (hj : j ∉ S) : A' (some j) = 0 := by
      by_cases hji : j = i
      · simp [A', coordinateReplaceIndex, hji, hnone]
      · simp [A', coordinateReplaceIndex, hji, hA j hj]
    obtain ⟨E⟩ := hprevious W S A b k.1 hnone hA
    obtain ⟨F⟩ := hprevious W S A' b' k.2 hnone' hA'
    obtain ⟨R⟩ := hmul hq E F
    have hcost : (q + c) ^ c ≤ (p + C) ^ C := by
      simpa [q, X, Polynomial.eval₂_pow] using hbudget p hp
    exact ⟨R.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

noncomputable def untranslatedMixedProduct {s : ℕ} {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
    (k : Fin 4 → Fin V.outputDim) (h₁ h₂ h₃ h₄ n : ℤ) : ℂ :=
  star (V.eval (k 0) (fun j => correlationInput h₁ n j.1)) *
    V.eval (k 1) (fun j => correlationInput h₂ n j.1) *
    V.eval (k 2) (fun j => correlationInput h₃ n j.1) *
    star (V.eval (k 3) (fun j => correlationInput h₄ n j.1))

noncomputable def mixedParallelogramProduct {s : ℕ} {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
    (k : Fin 4 → Fin V.outputDim) (x : Fin 4 → ℤ) : ℂ :=
  untranslatedMixedProduct V k (x 0) (x 1) (x 2) (x 1 + x 2 - x 0) (x 3)

theorem untranslatedMixedProduct_eq {s : ℕ} {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
    (k : Fin 4 → Fin V.outputDim) (h₁ h₂ h₃ h₄ n : ℤ)
    (hrel : -h₁ + h₂ + h₃ - h₄ = 0) :
    untranslatedMixedProduct V k h₁ h₂ h₃ h₄ n = mixedParallelogramProduct V k ![h₁, h₂, h₃, n] := by
  have hh₄ : h₄ = h₂ + h₃ - h₁ := by omega
  subst h₄
  rfl

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_replaced_mixed_translation_expansion (s : ℕ)
    (l : List (ReplicatedIndex (mixedCorrelationDegree s))) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
      (i : ReplicatedIndex (mixedCorrelationDegree s)), i.1 = 1 →
      ∀ (h δ : ℤ) (a : BinaryTensorIndex (Fin V.outputDim) l.length),
        Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) ((p + C) ^ C)
          (fun x => coordinateTranslationExpansion V.eval l a
            (coordinateReplaceInput i (mixedTranslationSample s ![h, x (), δ])))) := by
  obtain ⟨C, hC, hfreeze⟩ := exists_frozen_translation_expansion
    (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) l
  refine ⟨C, hC, ?_⟩
  intro p V i hi h δ a
  let S := (mixedEvaluationCoordinates s).erase i
  let A (j) := mixedTranslationSlope s (coordinateReplaceIndex i j)
  let b (j) := mixedTranslationIntercept s h δ (coordinateReplaceIndex i j)
  have hA : ∀ j, j ∉ S → A (some j) = 0 :=
    fun j hj => mixedTranslationSlope_replaced_vanishes s i j hj
  have hdegree : (∑ _j ∈ S, (1 : ℕ)) = s - 1 := by
    simpa only [Finset.sum_const, smul_eq_mul, mul_one] using
      mixedEvaluationCoordinates_erase_card s i hi
  have hinput (x : Unit → ℤ) : (fun j => b j + A j * x ()) =
      coordinateReplaceInput i (mixedTranslationSample s ![h, x (), δ]) := by
    change coordinateReplaceInput i
      (fun j => mixedTranslationIntercept s h δ j + mixedTranslationSlope s j * x ()) = _
    rw [mixedTranslationSample_affine]
  have R := hfreeze V S A b a (mixedTranslationSlope_replaced_none s i) hA
  simpa only [hdegree, hinput] using R

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_parallelogram_equivalence (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p),
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun k : Fin V.outputDim × Fin V.outputDim => fun x : Fin 4 → ℤ =>
          V.eval k.1 (fun j => correlationInput (x 1) (x 3) j.1) *
            V.eval k.2 (fun j => correlationInput (x 2) (x 3) j.1))
        (fun k : Fin V.outputDim × Fin V.outputDim => fun x : Fin 4 → ℤ =>
          V.eval k.1 (fun j => correlationInput (x 0) (x 3) j.1) *
            V.eval k.2 (fun j => correlationInput (x 1 + x 2 - x 0) (x 3) j.1)) := by
  obtain ⟨C, hC, hpair⟩ := exists_coordinate_parallelogram_equivalence
    (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1)
  refine ⟨C, hC, ?_⟩
  intro p V
  let v (i : Fin 4) : ((Fin 4 → ℤ) →+ ℤ) := ⟨⟨fun x => x i, rfl⟩, fun _ _ => rfl⟩
  have hv (i : Fin 4) (x : Fin 4 → ℤ) : v i x = x i := rfl
  have E := hpair V (mixedShiftCoordinate s) rfl (v 0) (v 1) (v 2) (v 3)
  have hdegree : (∑ _j : ReplicatedIndex (mixedCorrelationDegree s), (1 : ℕ)) - 1 = s := by
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, replicatedMixed_card,
      Nat.add_sub_cancel]
  simpa only [hdegree, hv, ← mixed_input_eq_coordinateConstant] using E

theorem exists_mixed_parallelogram_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
      (k : Fin 4 → Fin V.outputDim),
      Nonempty (NativeIntegerExpansion (fun _ : Fin 4 => 1) s ((p + C) ^ C)
        (mixedParallelogramProduct V k)) := by
  obtain ⟨C, hC, hpair⟩ := exists_mixed_parallelogram_equivalence s
  refine ⟨C, hC, ?_⟩
  intro p V k
  obtain ⟨R⟩ := (hpair V).expansion (k 1, k 2) (k 0, k 3)
  have heq : (fun x : Fin 4 → ℤ =>
      (V.eval (k 1) (fun j => correlationInput (x 1) (x 3) j.1) *
        V.eval (k 2) (fun j => correlationInput (x 2) (x 3) j.1)) *
      star (V.eval (k 0) (fun j => correlationInput (x 0) (x 3) j.1) *
        V.eval (k 3) (fun j => correlationInput (x 1 + x 2 - x 0) (x 3) j.1))) =
      mixedParallelogramProduct V k := by
    funext x
    simp only [mixedParallelogramProduct, untranslatedMixedProduct, star_mul]
    ring
  exact ⟨heq ▸ R⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

theorem exists_remainder_expansion_of_evaluation_coordinates (s : ℕ)
    (l : List (ReplicatedIndex (mixedCorrelationDegree s))) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p),
      (∀ i ∈ l, i.1 = 1) → ∀ (h δ : ℤ) (a : BinaryTensorIndex (Fin V.outputDim) l.length),
        Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) ((p + C) ^ C)
          (fun x => translationExpansionRemainder V.eval l a (mixedTranslationSample s ![h, x (), δ]))) := by
  induction l with
  | nil =>
    refine ⟨2, le_rfl, ?_⟩
    intro p V _ h δ a
    have hp : 0 ≤ p := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
    have hbudget : 2 ≤ (p + (2 : ℕ)) ^ (2 : ℕ) := by
      norm_num only [Nat.cast_ofNat]
      nlinarith only [hp, sq_nonneg p]
    exact ⟨NativeIntegerExpansion.constOne (fun _ : Unit => 1) (s - 1) hbudget⟩
  | cons i l ih =>
    obtain ⟨a, _, hprevious⟩ := ih
    obtain ⟨b, _, hright⟩ := exists_replaced_mixed_translation_expansion s l
    obtain ⟨c, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
    let X : Polynomial ℕ := Polynomial.X
    let Q := (X + Polynomial.C a) ^ a + (X + Polynomial.C b) ^ b + 2
    obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C c) ^ c)
    refine ⟨C, hC, ?_⟩
    intro p V hl h δ k
    have hp : 0 ≤ p := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
    let q := (p + a) ^ a + (p + b) ^ b + 2
    have ha : 0 ≤ (p + a) ^ a := by positivity
    have hb : 0 ≤ (p + b) ^ b := by positivity
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have haq : (p + a) ^ a ≤ q := by dsimp [q]; linarith only [hb]
    have hbq : (p + b) ^ b ≤ q := by dsimp [q]; linarith only [ha]
    obtain ⟨E⟩ := hprevious V (fun j hj => hl j (List.mem_cons_of_mem i hj)) h δ k.1
    obtain ⟨F⟩ := hright V i (hl i (List.mem_cons_self)) h δ k.2
    obtain ⟨R⟩ := hmul hq (E.mono haq) (F.mono hbq)
    have hcost : (q + c) ^ c ≤ (p + C) ^ C := by
      simpa [q, Q, X, Polynomial.eval₂_pow] using hbound p hp
    exact ⟨R.mono hcost⟩

theorem exists_mixed_remainder_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
      (h δ : ℤ)
      (a : BinaryTensorIndex (Fin V.outputDim) (mixedTranslationCoordinates s).length),
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) ((p + C) ^ C)
        (fun x => translationExpansionRemainder V.eval (mixedTranslationCoordinates s) a
          (mixedTranslationSample s ![h, x (), δ]))) := by
  obtain ⟨C, hC, hrem⟩ := exists_remainder_expansion_of_evaluation_coordinates s (mixedTranslationCoordinates s)
  exact ⟨C, hC, fun V h δ a => hrem V
    (fun i hi => (mem_mixedTranslationCoordinates s i).mp hi) h δ a⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_untranslated_mixed_reduction (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p),
      ∃ E : ∀ k : Fin 4 → Fin V.outputDim,
        NativeIntegerExpansion (fun _ : Fin 4 => 1) s ((p + C) ^ C) (mixedParallelogramProduct V k),
        ∀ {X : Type*} (S : Finset X) (h₁ h₂ h₃ h₄ n : X → ℤ)
          (k : Fin 4 → Fin V.outputDim) (f : X → ℂ) (q : ℝ),
          (∀ u ∈ S, -h₁ u + h₂ u + h₃ u - h₄ u = 0) →
          Real.exp (-q) ≤ ‖𝔼 u ∈ S, f u *
            untranslatedMixedProduct V k (h₁ u) (h₂ u) (h₃ u) (h₄ u) (n u)‖ →
          ∃ a : Fin (E k).count, Real.exp (-(q + (p + C) ^ C)) ≤
            ‖𝔼 u ∈ S, f u * ((E k).test a).eval ![h₁ u, h₂ u, h₃ u, n u]‖ := by
  obtain ⟨C, hC, hproduct⟩ := exists_mixed_parallelogram_expansion s
  refine ⟨C, hC, ?_⟩
  intro p V
  classical
  let E (k : Fin 4 → Fin V.outputDim) := Classical.choice (hproduct V k)
  refine ⟨E, ?_⟩
  intro X S h₁ h₂ h₃ h₄ n k f q hrel hcorr
  let sample (u : X) : Fin 4 → ℤ := ![h₁ u, h₂ u, h₃ u, n u]
  have hmean : (𝔼 u ∈ S, f u * untranslatedMixedProduct V k (h₁ u) (h₂ u) (h₃ u) (h₄ u) (n u)) =
      𝔼 u ∈ S, f u * mixedParallelogramProduct V k (sample u) := by
    apply Finset.expect_congr rfl
    intro u hu
    rw [untranslatedMixedProduct_eq V k (h₁ u) (h₂ u) (h₃ u) (h₄ u) (n u) (hrel u hu)]
  exact (E k).select_sample_product_correlation S sample f (by rwa [← hmean])

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

def MixedTranslationReductionStatement (s C : ℕ) : Prop :=
  ∀ {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p),
    ∃ E : NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun k (x : Fin 3 → ℤ) => V.eval k (fun j => correlationInput (x 0) (x 1 + x 2) j.1))
        (fun a x => coordinateTranslationExpansion V.eval (mixedTranslationCoordinates s) a
          (mixedTranslationSample s x)),
      ∀ h δ : ℤ, ∃ R : ∀ a : BinaryTensorIndex (Fin V.outputDim) (mixedTranslationCoordinates s).length,
        NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) ((p + C) ^ C)
          (fun x => translationExpansionRemainder V.eval (mixedTranslationCoordinates s) a
            (mixedTranslationSample s ![h, x (), δ])),
        ∀ {X : Type*} (S : Finset X) (n : X → ℤ) (k : Fin V.outputDim) (f : X → ℂ) (q : ℝ),
          Real.exp (-q) ≤ ‖𝔼 u ∈ S, f u * star
            (V.eval k (fun j => correlationInput h (n u + δ) j.1))‖ →
          ∃ (a : BinaryTensorIndex (Fin V.outputDim) (mixedTranslationCoordinates s).length)
            (b : Fin (E.selectedExpansion k a).count) (c : Fin (R a).count),
            Real.exp (-(q + 3 * (p + C) ^ C)) ≤ ‖𝔼 u ∈ S, f u * star
              (V.eval (firstTranslationCoordinate (mixedTranslationCoordinates s) a)
                  (fun j => correlationInput h (n u) j.1) *
                ((E.selectedExpansion k a).test b).eval ![h, n u, δ] *
                ((R a).test c).eval (fun _ => n u))‖

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem mixed_translation_reduction_transfer {s : ℕ} {p P : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
    (E : NativeIntegerVectorEquivalence s P
      (fun k (x : Fin 3 → ℤ) => V.eval k (fun j => correlationInput (x 0) (x 1 + x 2) j.1))
      (fun a x => coordinateTranslationExpansion V.eval (mixedTranslationCoordinates s) a
        (mixedTranslationSample s x)))
    (h δ : ℤ)
    (R : ∀ a : BinaryTensorIndex (Fin V.outputDim) (mixedTranslationCoordinates s).length,
      NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) P
        (fun x => translationExpansionRemainder V.eval (mixedTranslationCoordinates s) a
          (mixedTranslationSample s ![h, x (), δ])))
    {Y : Type*} (S : Finset Y) (n : Y → ℤ) (k : Fin V.outputDim) (f : Y → ℂ) (q : ℝ)
    (hcorr : Real.exp (-q) ≤ ‖𝔼 u ∈ S, f u * star
      (V.eval k (fun j => correlationInput h (n u + δ) j.1))‖) :
    ∃ (a : BinaryTensorIndex (Fin V.outputDim) (mixedTranslationCoordinates s).length)
      (b : Fin (E.selectedExpansion k a).count) (c : Fin (R a).count),
      Real.exp (-(q + 3 * P)) ≤ ‖𝔼 u ∈ S, f u * star
        (V.eval (firstTranslationCoordinate (mixedTranslationCoordinates s) a)
            (fun j => correlationInput h (n u) j.1) *
          ((E.selectedExpansion k a).test b).eval ![h, n u, δ] *
          ((R a).test c).eval (fun _ => n u))‖ := by
  let sample (u : Y) : Fin 3 → ℤ := ![h, n u, δ]
  have hc : Real.exp (-q) ≤ ‖𝔼 u ∈ S, f u * star
      (V.eval k (fun j => correlationInput (sample u 0) (sample u 1 + sample u 2) j.1))‖ := hcorr
  obtain ⟨j, v, hjv⟩ := E.transfer_sample_correlation S sample k f
    (fun u _ => coordinateTranslationExpansion_unit V.eval V.unit_eval
      (mixedTranslationCoordinates s) (mixedTranslationSample s (sample u))) hc
  let g (u : Y) := f u * star
    (V.eval (firstTranslationCoordinate (mixedTranslationCoordinates s) j)
        (fun z => correlationInput h (n u) z.1) *
      ((E.selectedExpansion k j).test v).eval (sample u))
  have hg : Real.exp (-(q + 2 * P)) ≤ ‖𝔼 u ∈ S, g u * star
      (translationExpansionRemainder V.eval (mixedTranslationCoordinates s) j
        (mixedTranslationSample s ![h, n u, δ]))‖ := by
    simpa only [V.mixedTranslationExpansion_factor, sample, Matrix.cons_val_zero,
      Matrix.cons_val_one, g, star_mul, mul_assoc, mul_left_comm, mul_comm] using hjv
  obtain ⟨w, hw⟩ := (R j).select_sample_correlation S (fun u (_ : Unit) => n u) g hg
  refine ⟨j, v, w, ?_⟩
  rw [show (q + 2 * P) + P = q + 3 * P by ring] at hw
  simpa only [g, sample, star_mul, mul_assoc, mul_left_comm, mul_comm] using hw

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

abbrev MixedExpansionIndex {s : ℕ} {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p) :=
  BinaryTensorIndex (Fin V.outputDim) (mixedTranslationCoordinates s).length

structure NativeMixedReductionData {s : ℕ} {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
    (P : ℝ) where
  budget_two : 2 ≤ P
  translation : NativeIntegerVectorEquivalence s P
    (fun k (x : Fin 3 → ℤ) => V.eval k (fun j => correlationInput (x 0) (x 1 + x 2) j.1))
    (fun a x => coordinateTranslationExpansion V.eval (mixedTranslationCoordinates s) a
      (mixedTranslationSample s x))
  lower : ∀ h δ : ℤ, ∀ a : MixedExpansionIndex V,
    NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) P
      (fun x => translationExpansionRemainder V.eval (mixedTranslationCoordinates s) a
        (mixedTranslationSample s ![h, x (), δ]))
  parallelogram : ∀ k : Fin 4 → Fin V.outputDim,
    NativeIntegerExpansion (fun _ : Fin 4 => 1) s P (mixedParallelogramProduct V k)

namespace NativeMixedReductionData

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

noncomputable def translationTerm (k : Fin V.outputDim) (a : MixedExpansionIndex V)
    (b : Fin (D.translation.selectedExpansion k a).count) (x : Fin 3 → ℤ) : ℂ :=
  ((D.translation.selectedExpansion k a).test b).eval x

noncomputable def lowerTerm (h δ : ℤ) (a : MixedExpansionIndex V)
    (c : Fin (D.lower h δ a).count) (n : ℤ) : ℂ :=
  ((D.lower h δ a).test c).eval (fun _ => n)

noncomputable def correction (h δ : ℤ) (k : Fin V.outputDim) (a : MixedExpansionIndex V)
    (b : Fin (D.translation.selectedExpansion k a).count) (c : Fin (D.lower h δ a).count) (n : ℤ) : ℂ :=
  V.eval (firstTranslationCoordinate (mixedTranslationCoordinates s) a) (fun j => correlationInput h n j.1) *
    D.translationTerm k a b ![h, n, δ] * D.lowerTerm h δ a c n

end NativeMixedReductionData

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

theorem exists_mixed_translation_reduction (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ MixedTranslationReductionStatement s C := by
  obtain ⟨a, _, hequiv⟩ := exists_mixed_translation_equivalence s
  obtain ⟨b, _, hrem⟩ := exists_mixed_remainder_expansion s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a) ^ a + (X + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p V
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  have ha : 0 ≤ (p + a) ^ a := by positivity
  have hb : 0 ≤ (p + b) ^ b := by positivity
  have hsum : (p + a) ^ a + (p + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have haC : (p + a) ^ a ≤ (p + C) ^ C := by linarith only [hb, hsum]
  have hbC : (p + b) ^ b ≤ (p + C) ^ C := by linarith only [ha, hsum]
  let E := (hequiv V).mono haC
  refine ⟨E, ?_⟩
  intro h δ
  let R (j : BinaryTensorIndex (Fin V.outputDim) (mixedTranslationCoordinates s).length) :
      NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) ((p + C) ^ C)
        (fun x => translationExpansionRemainder V.eval (mixedTranslationCoordinates s) j
          (mixedTranslationSample s ![h, x (), δ])) :=
    (Classical.choice (hrem V h δ j)).mono hbC
  refine ⟨R, ?_⟩
  intro Y S n k f q hcorr
  exact V.mixed_translation_reduction_transfer E h δ R S n k f q hcorr

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

noncomputable def translatedMixedProduct {s : ℕ} {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
    (k : Fin 4 → Fin V.outputDim) (h₁ h₂ h₃ h₄ δ n : ℤ) : ℂ :=
  fourPointProduct
    (fun n => V.eval (k 0) (fun j => correlationInput h₁ n j.1))
    (fun n => V.eval (k 1) (fun j => correlationInput h₂ n j.1))
    (fun n => V.eval (k 2) (fun j => correlationInput h₃ n j.1))
    (fun n => V.eval (k 3) (fun j => correlationInput h₄ n j.1)) δ n

namespace NativeMixedReductionData

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

structure TranslationCode (k : Fin 4 → Fin V.outputDim) where
  second : MixedExpansionIndex V
  fourth : MixedExpansionIndex V
  secondTerm : Fin (D.translation.selectedExpansion (k 1) second).count
  fourthTerm : Fin (D.translation.selectedExpansion (k 3) fourth).count

noncomputable def translationCoordinates (k : Fin 4 → Fin V.outputDim) (t : D.TranslationCode k) :
    Fin 4 → Fin V.outputDim :=
  ![k 0, firstTranslationCoordinate (mixedTranslationCoordinates s) t.second,
    k 2, firstTranslationCoordinate (mixedTranslationCoordinates s) t.fourth]

structure LowerCode {k : Fin 4 → Fin V.outputDim} (t : D.TranslationCode k) (h₂ h₄ δ : ℤ) where
  second : Fin (D.lower h₂ δ t.second).count
  fourth : Fin (D.lower h₄ δ t.fourth).count

noncomputable def translationGlobal (k : Fin 4 → Fin V.outputDim) (t : D.TranslationCode k)
    (x : Fin 5 → ℤ) : ℂ :=
  D.translationTerm (k 1) t.second t.secondTerm ![x 1, x 3, x 4] *
    star (D.translationTerm (k 3) t.fourth t.fourthTerm ![x 1 + x 2 - x 0, x 3, x 4])

noncomputable def translationLower {k : Fin 4 → Fin V.outputDim} (t : D.TranslationCode k)
    (h₂ h₄ δ : ℤ) (c : D.LowerCode t h₂ h₄ δ) (n : ℤ) : ℂ :=
  D.lowerTerm h₂ δ t.second c.second n * star (D.lowerTerm h₄ δ t.fourth c.fourth n)

theorem translationGlobal_sample (k : Fin 4 → Fin V.outputDim) (t : D.TranslationCode k)
    (h₁ h₂ h₃ h₄ n δ : ℤ) (hrel : -h₁ + h₂ + h₃ - h₄ = 0) :
    D.translationGlobal k t ![h₁, h₂, h₃, n, δ] =
      D.translationTerm (k 1) t.second t.secondTerm ![h₂, n, δ] *
        star (D.translationTerm (k 3) t.fourth t.fourthTerm ![h₄, n, δ]) := by
  have hh₄ : h₄ = h₂ + h₃ - h₁ := by omega
  subst h₄
  rfl

structure ReductionCode (k : Fin 4 → Fin V.outputDim) where
  translations : D.TranslationCode k
  term : Fin (D.parallelogram (D.translationCoordinates k translations)).count

noncomputable def globalError (k : Fin 4 → Fin V.outputDim) (a : D.ReductionCode k)
    (x : Fin 5 → ℤ) : ℂ :=
  D.translationGlobal k a.translations x *
    ((D.parallelogram (D.translationCoordinates k a.translations)).test a.term).eval
      ![x 0, x 1, x 2, x 3]

end NativeMixedReductionData

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem star_finite_expect {X : Type*} (S : Finset X) (f : X → ℂ) :
    star (𝔼 u ∈ S, f u) = 𝔼 u ∈ S, star (f u) := by
  simp [Finset.expect]

namespace NativeMixedReductionData

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

theorem translation_negative (h δ : ℤ) {X : Type*} (S : Finset X) (n : X → ℤ)
    (k : Fin V.outputDim) (f : X → ℂ) (q : ℝ)
    (hcorr : Real.exp (-q) ≤ ‖𝔼 u ∈ S, f u * star
      (V.eval k (fun j => correlationInput h (n u + δ) j.1))‖) :
    ∃ (a : MixedExpansionIndex V) (b : Fin (D.translation.selectedExpansion k a).count)
      (c : Fin (D.lower h δ a).count), Real.exp (-(q + 3 * P)) ≤
        ‖𝔼 u ∈ S, f u * star (D.correction h δ k a b c (n u))‖ :=
  V.mixed_translation_reduction_transfer D.translation h δ (D.lower h δ) S n k f q hcorr

theorem translation_positive (h δ : ℤ) {X : Type*} (S : Finset X) (n : X → ℤ)
    (k : Fin V.outputDim) (f : X → ℂ) (q : ℝ)
    (hcorr : Real.exp (-q) ≤ ‖𝔼 u ∈ S, f u *
      V.eval k (fun j => correlationInput h (n u + δ) j.1)‖) :
    ∃ (a : MixedExpansionIndex V) (b : Fin (D.translation.selectedExpansion k a).count)
      (c : Fin (D.lower h δ a).count), Real.exp (-(q + 3 * P)) ≤
        ‖𝔼 u ∈ S, f u * D.correction h δ k a b c (n u)‖ := by
  have hc : Real.exp (-q) ≤ ‖𝔼 u ∈ S, star (f u) * star
      (V.eval k (fun j => correlationInput h (n u + δ) j.1))‖ := by
    simpa only [← star_mul, ← star_finite_expect, norm_star, mul_comm] using hcorr
  obtain ⟨a, b, c, habc⟩ := D.translation_negative h δ S n k (fun u => star (f u)) q hc
  exact ⟨a, b, c, by simpa only [← star_mul, ← star_finite_expect, norm_star, mul_comm] using habc⟩

end NativeMixedReductionData

end Erdos3

end

section

namespace Erdos3.NativeMixedReductionData

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

theorem correction_factorization (k : Fin 4 → Fin V.outputDim) (t : D.TranslationCode k)
    (h₁ h₂ h₃ h₄ δ n : ℤ) (c : D.LowerCode t h₂ h₄ δ) (z : ℂ)
    (hrel : -h₁ + h₂ + h₃ - h₄ = 0) :
    z * star (V.eval (k 0) (fun j => correlationInput h₁ n j.1)) *
        V.eval (k 2) (fun j => correlationInput h₃ n j.1) *
        star (D.correction h₄ δ (k 3) t.fourth t.fourthTerm c.fourth n) *
        D.correction h₂ δ (k 1) t.second t.secondTerm c.second n =
      z * D.translationGlobal k t ![h₁, h₂, h₃, n, δ] *
        D.translationLower t h₂ h₄ δ c n *
        untranslatedMixedProduct V (D.translationCoordinates k t) h₁ h₂ h₃ h₄ n := by
  rw [D.translationGlobal_sample k t h₁ h₂ h₃ h₄ n δ hrel]
  have hzero : D.translationCoordinates k t 0 = k 0 := rfl
  have hone : D.translationCoordinates k t 1 =
      firstTranslationCoordinate (mixedTranslationCoordinates s) t.second := rfl
  have htwo : D.translationCoordinates k t 2 = k 2 := rfl
  have hthree : D.translationCoordinates k t 3 =
      firstTranslationCoordinate (mixedTranslationCoordinates s) t.fourth := rfl
  simp only [correction, translationLower, untranslatedMixedProduct,
    hzero, hone, htwo, hthree, star_mul]
  ring

end Erdos3.NativeMixedReductionData

end

section

namespace Erdos3.NativeMixedReductionData

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

noncomputable def translationTermExpansion (k : Fin V.outputDim) (a : MixedExpansionIndex V)
    (b : Fin (D.translation.selectedExpansion k a).count) :
    NativeIntegerExpansion (fun _ : Fin 3 => 1) s P (D.translationTerm k a b) :=
  NativeIntegerExpansion.ofTest ((D.translation.selectedExpansion k a).test b)
    ((D.translation.selectedExpansion k a).complexity b) (fun _ => rfl)

def secondInput (i : Fin 3) : ((Fin 5 → ℤ) →+ ℤ) where
  toFun x := (![x 1, x 3, x 4] : Fin 3 → ℤ) i
  map_zero' := by fin_cases i <;> rfl
  map_add' x y := by fin_cases i <;> rfl

def fourthInput (i : Fin 3) : ((Fin 5 → ℤ) →+ ℤ) where
  toFun x := (![x 1 + x 2 - x 0, x 3, x 4] : Fin 3 → ℤ) i
  map_zero' := by fin_cases i <;> rfl
  map_add' x y := by
    fin_cases i
    · change (x 1 + y 1) + (x 2 + y 2) - (x 0 + y 0) =
        (x 1 + x 2 - x 0) + (y 1 + y 2 - y 0)
      ring
    · rfl
    · rfl

def parallelogramInput (i : Fin 4) : ((Fin 5 → ℤ) →+ ℤ) where
  toFun x := (![x 0, x 1, x 2, x 3] : Fin 4 → ℤ) i
  map_zero' := by fin_cases i <;> rfl
  map_add' x y := by fin_cases i <;> rfl

noncomputable def translationGlobalExpansion (k : Fin 4 → Fin V.outputDim)
    (t : D.TranslationCode k) :
    NativeIntegerExpansion (fun _ : Fin 5 => 1) s (productNiltestBudget P + 2 * P)
      (D.translationGlobal k t) :=
  ((D.translationTermExpansion (k 1) t.second t.secondTerm).linearPullbackHom secondInput).mul
    (((D.translationTermExpansion (k 3) t.fourth t.fourthTerm).linearPullbackHom fourthInput).conjugate)
    D.budget_two

noncomputable def lowerTermExpansion (h δ : ℤ) (a : MixedExpansionIndex V)
    (c : Fin (D.lower h δ a).count) :
    NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) P
      (fun x => D.lowerTerm h δ a c (x ())) :=
  NativeIntegerExpansion.ofTest ((D.lower h δ a).test c) ((D.lower h δ a).complexity c)
    (fun _ => rfl)

noncomputable def translationLowerExpansion {k : Fin 4 → Fin V.outputDim}
    (t : D.TranslationCode k) (h₂ h₄ δ : ℤ) (c : D.LowerCode t h₂ h₄ δ) :
    NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) (productNiltestBudget P + 2 * P)
      (fun x => D.translationLower t h₂ h₄ δ c (x ())) :=
  (D.lowerTermExpansion h₂ δ t.second c.second).mul
    (D.lowerTermExpansion h₄ δ t.fourth c.fourth).conjugate D.budget_two

noncomputable def parallelogramTermExpansion (k : Fin 4 → Fin V.outputDim)
    (a : D.ReductionCode k) :
    NativeIntegerExpansion (fun _ : Fin 5 => 1) s P
      (fun x => ((D.parallelogram (D.translationCoordinates k a.translations)).test a.term).eval
        ![x 0, x 1, x 2, x 3]) :=
  (NativeIntegerExpansion.ofTest
    ((D.parallelogram (D.translationCoordinates k a.translations)).test a.term)
    ((D.parallelogram (D.translationCoordinates k a.translations)).complexity a.term)
    (fun _ => rfl)).linearPullbackHom parallelogramInput

end Erdos3.NativeMixedReductionData

end

section

namespace Erdos3

def mixedErrorPairBudget (p : ℝ) : ℝ := productNiltestBudget p + 2 * p

def mixedErrorBudget (p : ℝ) : ℝ :=
  productNiltestBudget (mixedErrorPairBudget p) + 2 * mixedErrorPairBudget p

theorem le_mixedErrorPairBudget {p : ℝ} (hp : 0 ≤ p) : p ≤ mixedErrorPairBudget p := by
  have h := productNiltestBudget_geometry hp
  unfold mixedErrorPairBudget
  nlinarith only [hp, h, sq_nonneg (p + 2)]

namespace NativeMixedReductionData

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

noncomputable def globalErrorExpansion (k : Fin 4 → Fin V.outputDim)
    (a : D.ReductionCode k) :
    NativeIntegerExpansion (fun _ : Fin 5 => 1) s (mixedErrorBudget P) (D.globalError k a) := by
  have hp : 0 ≤ P := le_trans (by norm_num) D.budget_two
  have hP : P ≤ mixedErrorPairBudget P := le_mixedErrorPairBudget hp
  exact (D.translationGlobalExpansion k a.translations).mul
    ((D.parallelogramTermExpansion k a).mono hP) (D.budget_two.trans hP)

end NativeMixedReductionData

theorem exists_mixed_error_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      mixedErrorPairBudget p ≤ (p + C) ^ C ∧ mixedErrorBudget p ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + 2) ^ 2 + X + (X + (X ^ 2 + X + 3) ^ 2) + X ^ 2 + 4 + 2 * X
  let T := (R + 2) ^ 2 + R + (R + (R ^ 2 + R + 3) ^ 2) + R ^ 2 + 4 + 2 * R
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + T)
  refine ⟨C, hC, fun p hp => ?_⟩
  have hpair : 0 ≤ mixedErrorPairBudget p := hp.trans (le_mixedErrorPairBudget hp)
  have hglobal : 0 ≤ mixedErrorBudget p := by
    change 0 ≤ mixedErrorPairBudget (mixedErrorPairBudget p)
    exact hpair.trans (le_mixedErrorPairBudget hpair)
  have hb : mixedErrorPairBudget p + mixedErrorBudget p ≤ (p + C) ^ C := by
    simpa [X, R, T, mixedErrorPairBudget, mixedErrorBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget p hp
  constructor <;> linarith only [hpair, hglobal, hb]

end Erdos3

end

section

namespace Erdos3.NativeIntegerExpansion

noncomputable def translate {s : ℕ} {p : ℝ} {f : ℤ → ℂ}
    (E : NativeIntegerExpansion (fun _ : Unit => 1) s p (fun x => f (x ()))) (δ : ℤ) :
    NativeIntegerExpansion (fun _ : Unit => 1) s p (fun x => f (x () + δ)) := by
  simpa [integerAffineMap, add_comm] using E.affinePullback (fun (_ : Unit) (_ : Unit) => (1 : ℤ)) (fun _ => δ)

noncomputable def fourPoint {s : ℕ} {p : ℝ} (f : Fin 4 → ℤ → ℂ)
    (E : ∀ i, NativeIntegerExpansion (fun _ : Unit => 1) s p (fun x => f i (x ())))
    (hp : 2 ≤ p) (δ : ℤ) :
    NativeIntegerExpansion (fun _ : Unit => 1) s (mixedErrorBudget p)
      (fun x => fourPointProduct (f 0) (f 1) (f 2) (f 3) δ (x ())) := by
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hpair : 2 ≤ mixedErrorPairBudget p := hp.trans (le_mixedErrorPairBudget hp0)
  let E₁₂ := (E 0).conjugate.mul ((E 1).translate δ) hp
  let E₃₄ := (E 2).mul ((E 3).translate δ).conjugate hp
  simpa only [mixedErrorBudget, mixedErrorPairBudget, fourPointProduct, mul_assoc] using E₁₂.mul E₃₄ hpair

end Erdos3.NativeIntegerExpansion

end

section

namespace Erdos3

open scoped BigOperators

theorem native_weight_pair_removal {I : Type} [Fintype I] [Nonempty I]
    {d : ℕ} {p : ℝ} (hp : 2 ≤ p) (A : Finset ℤ) (hA : A.Nonempty)
    (S : I → Finset ℤ) (hSA : ∀ i, S i ⊆ A)
    (weight : ℤ → ℂ) (a v : I → ℤ → ℂ)
    (E : ∀ i, NativeIntegerExpansion (fun _ : Unit => 1) d p (fun x => v i (x ())))
    (hw : ∀ x ∈ A, ‖weight x‖ ≤ 1) (ha : ∀ i x, x ∈ S i → ‖a i x‖ ≤ 1)
    (hsize : ∀ i, Real.exp (-p) ≤ (S i).card / (A.card : ℝ))
    (hcorr : ∀ i, Real.exp (-p) ≤ ‖𝔼 x ∈ S i, weight x * (a i x * v i x)‖) :
    ∃ P : Finset (I × I), P.Nonempty ∧
      Real.exp (-(8 * p + 1)) * (Fintype.card I : ℝ) ^ 2 ≤ (P.card : ℝ) ∧
      ∀ t ∈ P, (S t.1 ∩ S t.2).Nonempty ∧
        Real.exp (-(8 * p + 1)) ≤ (S t.1 ∩ S t.2).card / (A.card : ℝ) ∧
        Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) d (mixedErrorPairBudget p)
          (fun x => v t.1 (x ()) * star (v t.2 (x ())))) ∧
        Real.exp (-(8 * p + 1)) ≤ ‖𝔼 x ∈ S t.1 ∩ S t.2,
          (a t.1 x * star (a t.2 x)) * (v t.1 x * star (v t.2 x))‖ := by
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  let u (i : I) (x : ℤ) := (Real.exp (-(2 * p)) : ℂ) * (a i x * v i x)
  have hu (i : I) (x : ℤ) (hx : x ∈ S i) : ‖u i x‖ ≤ 1 := by
    apply exp_scaled_norm_le_one
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (ha i x hx) ((E i).norm_eval_le (fun _ => x))
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have huc (i : I) : Real.exp (-(3 * p)) ≤ ‖𝔼 x ∈ S i, weight x * u i x‖ := by
    have heq : (𝔼 x ∈ S i, weight x * u i x) =
        (Real.exp (-(2 * p)) : ℂ) * (𝔼 x ∈ S i, weight x * (a i x * v i x)) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      dsimp only [u]
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ = Real.exp (-(2 * p)) * Real.exp (-p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcorr i) (Real.exp_nonneg _)
  obtain ⟨P, hP, hPsize, hpair⟩ := exists_supported_correlation_pairs A hA S hSA
    weight u (Real.exp_pos (-p)) (Real.exp_pos (-(3 * p))) hw hu hsize huc
  have hthreshold : Real.exp (-(8 * p + 1)) ≤ (Real.exp (-p) * Real.exp (-(3 * p))) ^ 2 / 2 := by
    have heq : (Real.exp (-p) * Real.exp (-(3 * p))) ^ 2 = Real.exp (-(8 * p)) := by
      rw [← Real.exp_add, ← Real.exp_nat_mul]
      congr 1
      ring
    rw [heq]
    simpa only [show -(8 * p + 1) = -(8 * p) - 1 by ring] using exp_sub_one_le_half_exp (-(8 * p))
  refine ⟨P, hP, (mul_le_mul_of_nonneg_right hthreshold (sq_nonneg _)).trans hPsize, ?_⟩
  intro t ht
  obtain ⟨hJ, hcor, hvol⟩ := hpair t ht
  refine ⟨hJ, hthreshold.trans hvol, ⟨(E t.1).mul (E t.2).conjugate hp⟩, ?_⟩
  have hcoef : (Real.exp (-(4 * p)) : ℂ) =
      (Real.exp (-(2 * p)) : ℂ) * (Real.exp (-(2 * p)) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 1
    ring_nf
  have hmean : (𝔼 x ∈ S t.1 ∩ S t.2, u t.1 x * star (u t.2 x)) =
      𝔼 x ∈ S t.1 ∩ S t.2, ((Real.exp (-(4 * p)) : ℂ) * (a t.1 x * star (a t.2 x))) *
        (v t.1 x * star (v t.2 x)) := by
    apply Finset.expect_congr rfl
    intro x _
    simp only [u, star_mul, Complex.star_def, Complex.conj_ofReal, hcoef]
    ring
  have hc := hthreshold.trans hcor
  rw [hmean] at hc
  exact finite_remove_normalization (S t.1 ∩ S t.2)
    (fun x => a t.1 x * star (a t.2 x)) (fun x => v t.1 x * star (v t.2 x))
    (by linarith : 0 ≤ 4 * p) hc

end Erdos3

end

end OAI
