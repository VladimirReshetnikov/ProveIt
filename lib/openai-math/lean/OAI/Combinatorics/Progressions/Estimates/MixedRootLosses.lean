/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.BinaryTupleSorting
import OAI.Combinatorics.Progressions.Estimates.OriginalMixedRootEquivalence

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def mixedSwapSample {s : ℕ} (π : Fin (s + 3) → Fin 2) : Fin (s + 3) → Fin 2 :=
  fun k => π (mixedExchangeCoordinate (s + 1) k)

theorem mixedSwapSample_input {s : ℕ} (π : Fin (s + 3) → Fin 2) (x : Fin 2 → ℤ) :
    mixedSampledInput (mixedSwapSample π) x =
      mixedSlotInput (x (π 1)) (x (π 0)) (fun j => x (π j.succ.succ)) := by
  rw [mixedSampledInput_slots]
  rfl

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def divisionMixedExchangeCorrection (d : ℕ)
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (π : Fin (s + 3) → Fin 2) (a b : Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  complexCrossContraction
    ((W.rationalDilation ((d : ℚ)⁻¹)).eval a (mixedSampledInput π x))
    ((W.rationalDilation ((d : ℚ)⁻¹)).eval b (mixedSampledInput (mixedSwapSample π) x))
    (fun i => W.eval i (mixedSampledInput π (fun k => x k / (d : ℤ))))
    (fun j => W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => x k / (d : ℤ))))
    (fun i j => G π i j (fun k => x k / (d : ℤ)))

theorem divisionMixedExchangeCorrection_pointwise_error (d : ℕ)
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (π : Fin (s + 3) → Fin 2) (a b : Fin W.outputDim) (x : Fin 2 → ℤ) :
    ‖(W.rationalDilation ((d : ℚ)⁻¹)).eval a (mixedSampledInput π x) *
        star ((W.rationalDilation ((d : ℚ)⁻¹)).eval b (mixedSampledInput (mixedSwapSample π) x)) -
      W.divisionMixedExchangeCorrection d G π a b x‖ ≤
      ∑ ij : Fin W.outputDim × Fin W.outputDim,
        ‖W.eval ij.1 (mixedSampledInput π (fun k => x k / (d : ℤ))) *
            star (W.eval ij.2 (mixedSampledInput (mixedSwapSample π) (fun k => x k / (d : ℤ)))) -
          G π ij.1 ij.2 (fun k => x k / (d : ℤ))‖ := by
  exact norm_sub_complexCrossContraction_le_sum _ _ _ _ _
    ((W.rationalDilation ((d : ℚ)⁻¹)).norm_eval _ _) ((W.rationalDilation ((d : ℚ)⁻¹)).norm_eval _ _)
    (W.unit_eval _) (W.unit_eval _) (fun i => W.norm_eval i _) (fun j => W.norm_eval j _)

theorem divisionMixedExchangeCorrection_mean_error (d : ℕ) [NeZero d]
    {N : ℕ} [NeZero N] {ε : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (π : Fin (s + 3) → Fin 2) (a b : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖(W.rationalDilation ((d : ℚ)⁻¹)).eval a (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star ((W.rationalDilation ((d : ℚ)⁻¹)).eval b
            (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        W.divisionMixedExchangeCorrection d G π a b (fun k => ((x k).val : ℤ))‖) ≤
      (d : ℝ) ^ 2 * (W.outputDim : ℝ) ^ 2 * ε := by
  have hmean := Finset.expect_le_expect (s := Finset.univ)
    (fun (x : Fin 2 → ZMod N) _ => W.divisionMixedExchangeCorrection_pointwise_error d G π a b
      (fun k => ((x k).val : ℤ)))
  rw [Finset.expect_sum_comm] at hmean
  have he (ij : Fin W.outputDim × Fin W.outputDim) :
      (𝔼 x : Fin 2 → ZMod N,
        ‖W.eval ij.1 (mixedSampledInput π (fun k => ((x k).val : ℤ) / (d : ℤ))) *
            star (W.eval ij.2 (mixedSampledInput (mixedSwapSample π)
              (fun k => ((x k).val : ℤ) / (d : ℤ)))) -
          G π ij.1 ij.2 (fun k => ((x k).val : ℤ) / (d : ℤ))‖) ≤ (d : ℝ) ^ 2 * ε := by
    have h := expect_pair_cyclicDivision_le d (fun x : Fin 2 → ZMod N =>
      ‖W.eval ij.1 (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval ij.2 (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π ij.1 ij.2 (fun k => ((x k).val : ℤ))‖) (fun _ => norm_nonneg _)
    simp only [cyclicDivision_val, Int.natCast_ediv] at h
    exact h.trans (mul_le_mul_of_nonneg_left (herr π ij.1 ij.2) (sq_nonneg _))
  apply hmean.trans
  calc
    _ ≤ ∑ _ : Fin W.outputDim × Fin W.outputDim, (d : ℝ) ^ 2 * ε :=
      Finset.sum_le_sum (fun ij _ => he ij)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul]
      ring

theorem divisionMixedExchangeCorrection_norm (d : ℕ) [NeZero d]
    {N : ℕ} [NeZero N] {B : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (π : Fin (s + 3) → Fin 2) (a b : Fin W.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.divisionMixedExchangeCorrection d G π a b (fun k => ((x k).val : ℤ))‖ ≤
      (W.outputDim : ℝ) ^ 2 * B := by
  unfold divisionMixedExchangeCorrection complexCrossContraction
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _ : Fin W.outputDim × Fin W.outputDim, B := by
      apply Finset.sum_le_sum
      intro ij _
      rw [norm_mul]
      apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans
      · have h := hG π ij.1 ij.2 (fun k => cyclicDivision d (x k))
        simpa only [cyclicDivision_val, Int.natCast_ediv] using h
      · rw [norm_mul, norm_star, norm_mul, norm_star, norm_mul, norm_star]
        exact (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          ((mul_le_of_le_one_left (norm_nonneg _)
            ((W.rationalDilation ((d : ℚ)⁻¹)).norm_eval _ _)).trans (W.norm_eval _ _))).trans
          ((mul_le_of_le_one_left (norm_nonneg _)
            ((W.rationalDilation ((d : ℚ)⁻¹)).norm_eval _ _)).trans (W.norm_eval _ _))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul, pow_two]

theorem exists_divisionMixedExchangeCorrection_expansion (s d : ℕ) [NeZero d] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p), 0 ≤ q →
      ∀ G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ π i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (G π i j))) →
      ∀ π a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + q + C) ^ C)
        (W.divisionMixedExchangeCorrection d G π a b)) := by
  obtain ⟨A, _, hcompare⟩ := exists_mixed_rational_division_equivalence s d
  obtain ⟨B, _, hdivision⟩ := NativeIntegerExpansion.exists_division_expansion d (s + 2) (by omega)
  obtain ⟨D, _, hcontract⟩ := exists_native_cross_contraction
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro p q W hq G hG π a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let t := (p + q + A) ^ A + (p + q + B) ^ B
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hAt : (p + A) ^ A ≤ t := by
    apply le_trans _ (le_add_of_nonneg_right (by positivity))
    exact pow_le_pow_left₀ (by positivity) (by linarith) A
  have hBt : (q + B) ^ B ≤ t := by
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    exact pow_le_pow_left₀ (by positivity) (by linarith) B
  have hF (i j : Fin W.outputDim) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) t
      (fun x => G π i j (fun k => x k / (d : ℤ)))) :=
    ⟨(Classical.choice (hdivision hq (Classical.choice (hG π i j)))).mono hBt⟩
  have H := hcontract (fun i j x => G π i j (fun k => x k / (d : ℤ))) ht
    ((hcompare W π).mono hAt) ((hcompare W (mixedSwapSample π)).mono hAt) hF a b
  have hcost : (t + D) ^ D ≤ (p + q + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget (p + q) (add_nonneg hp hq)
  exact ⟨(Classical.choice H).mono hcost⟩

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

theorem exists_division_mixed_last_slots_equivalence (d D : ℕ) [NeZero D] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p),
      (∀ (a : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) i x,
        W.eval i (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) a).symm j)) = W.eval i x) →
      ∀ (e : Equiv.Perm (Fin (d + 2))) (π : Fin (d + 3) → Fin 2),
      NativeIntegerVectorEquivalence (d + 2) ((p + C) ^ C)
        (fun i (x : Fin 2 → ℤ) => (W.rationalDilation ((D : ℚ)⁻¹)).eval i (mixedSampledInput π x))
        (fun i x => (W.rationalDilation ((D : ℚ)⁻¹)).eval i
          (mixedSampledInput (mixedPermuteSample e π) x)) := by
  obtain ⟨A, _, hcompare⟩ := exists_mixed_rational_division_equivalence d D
  obtain ⟨B, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W hsymm e π
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hu : 0 ≤ (p + A) ^ A := by positivity
  have heq : (fun i (x : Fin 2 → ℤ) => W.eval i (mixedSampledInput π (fun k => x k / (D : ℤ)))) =
      (fun i x => W.eval i (mixedSampledInput (mixedPermuteSample e π) (fun k => x k / (D : ℤ)))) := by
    funext i x
    symm
    change W.eval i (mixedReplicatedInput (x (π 0) / (D : ℤ)) (fun j => x (π (e j).succ) / (D : ℤ))) =
      W.eval i (mixedReplicatedInput (x (π 0) / (D : ℤ)) (fun j => x (π j.succ) / (D : ℤ)))
    exact W.mixed_permutation_eval hsymm e i (x (π 0) / (D : ℤ)) (fun j => x (π j.succ) / (D : ℤ))
  have F : NativeIntegerVectorEquivalence (d + 2) ((p + A) ^ A)
      (fun i (x : Fin 2 → ℤ) => W.eval i (mixedSampledInput π (fun k => x k / (D : ℤ))))
      (fun i x => (W.rationalDilation ((D : ℚ)⁻¹)).eval i
        (mixedSampledInput (mixedPermuteSample e π) x)) := by
    rw [heq]
    exact (hcompare W (mixedPermuteSample e π)).symm
  have H := htrans hu (hcompare W π) F (fun x => W.unit_eval _)
  have hcost : ((p + A) ^ A + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  exact H.mono hcost

theorem exists_division_mixed_tensor_last_slots_equivalence (d D n : ℕ) [NeZero D] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p),
      (∀ (a : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) i x,
        W.eval i (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) a).symm j)) = W.eval i x) →
      ∀ (e : Equiv.Perm (Fin (d + 2))) (π : Fin (d + 3) → Fin 2),
      NativeIntegerVectorEquivalence (d + 2) ((p + C) ^ C)
        (fun i (x : Fin 2 → ℤ) => ((W.rationalDilation ((D : ℚ)⁻¹)).tensorPower n).eval i (mixedSampledInput π x))
        (fun i x => ((W.rationalDilation ((D : ℚ)⁻¹)).tensorPower n).eval i (mixedSampledInput (mixedPermuteSample e π) x)) := by
  obtain ⟨A, _, hdivision⟩ := exists_division_mixed_last_slots_equivalence d D
  obtain ⟨B, _, htensor⟩ := NativeIntegerVectorEquivalence.exists_tensor_power_budget n
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W hsymm e π
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hu : 0 ≤ (p + A) ^ A := by positivity
  have H := htensor hu (hdivision W hsymm e π)
  have hcost : ((p + A) ^ A + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have E := H.mono hcost
  have hdim : (Fintype.card (Fin ((W.rationalDilation ((D : ℚ)⁻¹)).tensorPower n).outputDim) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    rw [Fintype.card_fin]
    change ((W.outputDim ^ n : ℕ) : ℝ) ≤ _
    have h := E.left_dimension
    simp only [Fintype.card_fun, Fintype.card_fin] at h
    change ((W.outputDim ^ n : ℕ) : ℝ) ≤ _ at h
    exact h
  apply E.of_coordinate_maps _ _ (tensorIndexEquiv W.outputDim n).symm
    (tensorIndexEquiv W.outputDim n).symm _ _ hdim hdim (le_refl _)
  · intro i x
    exact (W.rationalDilation ((D : ℚ)⁻¹)).tensorPower_eval n i (mixedSampledInput π x)
  · intro i x
    exact (W.rationalDilation ((D : ℚ)⁻¹)).tensorPower_eval n i
      (mixedSampledInput (mixedPermuteSample e π) x)

theorem exists_mixed_root_last_slots_equivalence (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p),
      (∀ (a : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) i x,
        W.eval i (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) a).symm j)) = W.eval i x) →
      ∀ (e : Equiv.Perm (Fin (d + 2))) (π : Fin (d + 3) → Fin 2),
      NativeIntegerVectorEquivalence (d + 2) ((p + C) ^ C)
        (fun i (x : Fin 2 → ℤ) => W.mixedIntegrationRoot.eval i (mixedSampledInput π x))
        (fun i x => W.mixedIntegrationRoot.eval i (mixedSampledInput (mixedPermuteSample e π) x)) := by
  obtain ⟨C, hC, h⟩ := exists_division_mixed_tensor_last_slots_equivalence d (d + 3) ((d + 3) ^ (d + 2))
  refine ⟨C, hC, ?_⟩
  intro p W hsymm e π
  exact h W hsymm e π

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedTensorExchangeCorrection (n : ℕ)
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (π : Fin (s + 3) → Fin 2) (a b : Fin (W.outputDim ^ n)) (x : Fin 2 → ℤ) : ℂ :=
  ∏ k : Fin n, G π ((tensorIndexEquiv W.outputDim n).symm a k)
    ((tensorIndexEquiv W.outputDim n).symm b k) x

theorem mixedTensorExchange_kernel (n : ℕ) (π : Fin (s + 3) → Fin 2)
    (a b : Fin (W.outputDim ^ n)) (x : Fin 2 → ℤ) :
    (W.tensorPower n).eval a (mixedSampledInput π x) *
        star ((W.tensorPower n).eval b (mixedSampledInput (mixedSwapSample π) x)) =
      ∏ k : Fin n, W.eval ((tensorIndexEquiv W.outputDim n).symm a k) (mixedSampledInput π x) *
        star (W.eval ((tensorIndexEquiv W.outputDim n).symm b k)
          (mixedSampledInput (mixedSwapSample π) x)) := by
  simp only [tensorPower_eval, star_prod, Finset.prod_mul_distrib]

theorem mixedTensorExchangeCorrection_norm (n : ℕ) {N : ℕ} [NeZero N] {B : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (π : Fin (s + 3) → Fin 2) (a b : Fin (W.outputDim ^ n)) (x : Fin 2 → ZMod N) :
    ‖W.mixedTensorExchangeCorrection n G π a b (fun k => ((x k).val : ℤ))‖ ≤ B ^ n := by
  rw [mixedTensorExchangeCorrection, norm_prod]
  calc
    _ ≤ ∏ _ : Fin n, B := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun _ _ => hG _ _ _ x)
    _ = _ := by simp

theorem mixedTensorExchangeCorrection_mean_error (n : ℕ) {N : ℕ} [NeZero N] {B ε : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) (hB : 1 ≤ B)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (π : Fin (s + 3) → Fin 2) (a b : Fin (W.outputDim ^ n)) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖(W.tensorPower n).eval a (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star ((W.tensorPower n).eval b
            (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        W.mixedTensorExchangeCorrection n G π a b (fun k => ((x k).val : ℤ))‖) ≤ B ^ n * (n * ε) := by
  let i := (tensorIndexEquiv W.outputDim n).symm a
  let j := (tensorIndexEquiv W.outputDim n).symm b
  have h := mean_prod_error_le
    (fun k (x : Fin 2 → ZMod N) =>
      W.eval (i k) (mixedSampledInput π (fun l => ((x l).val : ℤ))) *
        star (W.eval (j k) (mixedSampledInput (mixedSwapSample π) (fun l => ((x l).val : ℤ)))))
    (fun k (x : Fin 2 → ZMod N) => G π (i k) (j k) (fun l => ((x l).val : ℤ))) hB
    (fun k x => (by
      rw [norm_mul, norm_star]
      exact ((mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans
        (W.norm_eval _ _)).trans hB))
    (fun _ x => hG _ _ _ x) (fun k => herr π (i k) (j k))
  simpa only [Fintype.card_fin, mixedTensorExchange_kernel, mixedTensorExchangeCorrection, i, j] using h

theorem exists_mixedTensorExchangeCorrection_expansion (s n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p), 0 ≤ q →
      ∀ G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ π i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (G π i j))) →
      ∀ π a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((q + C) ^ C)
        (W.mixedTensorExchangeCorrection n G π a b)) := by
  obtain ⟨C, hC, hprod⟩ := NativeIntegerExpansion.exists_fin_prod_budget n
  refine ⟨C, hC, ?_⟩
  intro p q W hq G hG π a b
  exact hprod _ hq (fun _ => hG _ _ _)

theorem dilationTensorMixedExchangeCorrection_mean_error (d n : ℕ) [NeZero d]
    {N : ℕ} [NeZero N] {ε : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (π : Fin (s + 3) → Fin 2) (a b : Fin (W.outputDim ^ n)) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖((W.rationalDilation ((d : ℚ)⁻¹)).tensorPower n).eval a
            (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (((W.rationalDilation ((d : ℚ)⁻¹)).tensorPower n).eval b
            (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        (W.rationalDilation ((d : ℚ)⁻¹)).mixedTensorExchangeCorrection n
          (W.divisionMixedExchangeCorrection d G) π a b (fun k => ((x k).val : ℤ))‖) ≤
      (W.outputDim : ℝ) ^ (2 * n) * (n * ((d : ℝ) ^ 2 * (W.outputDim : ℝ) ^ 2 * ε)) := by
  have hd : (1 : ℝ) ≤ W.outputDim := by exact_mod_cast W.output_pos
  have hB : 1 ≤ (W.outputDim : ℝ) ^ 2 := by nlinarith
  have hH (π : Fin (s + 3) → Fin 2) (i j : Fin W.outputDim) (x : Fin 2 → ZMod N) :
      ‖W.divisionMixedExchangeCorrection d G π i j (fun k => ((x k).val : ℤ))‖ ≤ (W.outputDim : ℝ) ^ 2 := by
    simpa only [mul_one] using W.divisionMixedExchangeCorrection_norm d G hG π i j x
  have h := (W.rationalDilation ((d : ℚ)⁻¹)).mixedTensorExchangeCorrection_mean_error n
    (W.divisionMixedExchangeCorrection d G) hB hH
    (W.divisionMixedExchangeCorrection_mean_error d G herr) π a b
  simpa only [← pow_mul] using h

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

def mixedCornerWeight {s : ℕ} (v : Fin (s + 3) → Fin 2) : ℕ := ∑ k, (v k).val

def mixedCornerSample {s : ℕ} (v : Fin (s + 3) → Fin 2) : Fin (s + 3) → Fin 2 :=
  fun k => (v k).rev

def mixedCanonicalSample {s : ℕ} (v : Fin (s + 3) → Fin 2) : Fin (s + 3) → Fin 2 :=
  fun k => if k.val < mixedCornerWeight v then 0 else 1

def mixedTailSortPermutation {s : ℕ} (v : Fin (s + 3) → Fin 2) : Equiv.Perm (Fin (s + 2)) :=
  Tuple.sort (fun j => mixedCornerSample v j.succ)

noncomputable def mixedHeadIndex {s : ℕ} (v : Fin (s + 3) → Fin 2) : Fin (s + 2) :=
  if h : ∃ j : Fin (s + 2), v j.succ = 1 then Classical.choose h else 0

noncomputable def mixedHeadPermutation {s : ℕ} (v : Fin (s + 3) → Fin 2) :
    Equiv.Perm (Fin (s + 2)) := Equiv.swap 0 (mixedHeadIndex v)

noncomputable def mixedPreExchangeSample {s : ℕ} (v : Fin (s + 3) → Fin 2) : Fin (s + 3) → Fin 2 :=
  mixedPermuteSample (mixedHeadPermutation v) (mixedCornerSample v)

noncomputable def mixedPostExchangePermutation {s : ℕ} (v : Fin (s + 3) → Fin 2) :
    Equiv.Perm (Fin (s + 2)) :=
  Tuple.sort (fun j => mixedSwapSample (mixedPreExchangeSample v) j.succ)

def mixedExchangePermutation (s : ℕ) : Equiv.Perm (Fin (s + 3)) where
  toFun := mixedExchangeCoordinate (s + 1)
  invFun := mixedExchangeCoordinate (s + 1)
  left_inv := mixedExchangeCoordinate_involutive (s + 1)
  right_inv := mixedExchangeCoordinate_involutive (s + 1)

theorem mixedPermuteSample_eq_comp {s : ℕ} (e : Equiv.Perm (Fin (s + 2)))
    (π : Fin (s + 3) → Fin 2) : mixedPermuteSample e π = π ∘ zeroFixedPermutation e := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;> rfl

theorem mixedCornerSample_input {s : ℕ} (v : Fin (s + 3) → Fin 2) (x : Fin 2 → ℤ) :
    mixedDiagonalCorner v x = mixedSampledInput (mixedCornerSample v) x := rfl

theorem mixedCornerSample_zeroCount {s : ℕ} (v : Fin (s + 3) → Fin 2) :
    binaryZeroCount (mixedCornerSample v) = mixedCornerWeight v := by
  rw [binaryZeroCount, Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  change (if (v i).rev = 0 then 1 else 0) = (v i).val
  have H (b : Fin 2) : (if b.rev = 0 then 1 else 0) = b.val := by
    fin_cases b <;> decide
  exact H (v i)

theorem mixedCanonicalSample_eq_sorted {s : ℕ} (v : Fin (s + 3) → Fin 2) :
    mixedCanonicalSample v = binarySorted (mixedCornerSample v) := by
  funext k
  rw [binarySorted_threshold, mixedCornerSample_zeroCount]
  rfl

theorem mixedCanonicalSample_of_first_one {s : ℕ} (v : Fin (s + 3) → Fin 2) (h0 : v 0 = 1) :
    mixedCanonicalSample v = mixedPermuteSample (mixedTailSortPermutation v) (mixedCornerSample v) := by
  rw [mixedCanonicalSample_eq_sorted, mixedPermuteSample_eq_comp]
  exact binarySorted_tail _ (by change (v 0).rev = 0; rw [h0]; rfl)

theorem mixedCorner_exists_tail_one {s : ℕ} (v : MixedNonconstantCorner s) (h0 : v.val 0 = 0) :
    ∃ j : Fin (s + 2), v.val j.succ = 1 := by
  classical
  by_contra h
  apply v.property
  funext j
  refine Fin.cases h0 (fun j => ?_) j
  exact binary_eq_zero_of_ne_one _ (fun hj => h ⟨j, hj⟩)

theorem mixedHeadIndex_one {s : ℕ} (v : MixedNonconstantCorner s) (h0 : v.val 0 = 0) :
    v.val (mixedHeadIndex v.val).succ = 1 := by
  have h := mixedCorner_exists_tail_one v h0
  simp only [mixedHeadIndex, dite_eq_left h]
  exact Classical.choose_spec h

theorem mixedPreExchangeSample_one {s : ℕ} (v : MixedNonconstantCorner s) (h0 : v.val 0 = 0) :
    mixedPreExchangeSample v.val 1 = 0 := by
  change (v.val ((Equiv.swap 0 (mixedHeadIndex v.val)) 0).succ).rev = 0
  rw [Equiv.swap_apply_left, mixedHeadIndex_one v h0]
  rfl

theorem mixedCanonicalSample_of_first_zero {s : ℕ} (v : MixedNonconstantCorner s)
    (h0 : v.val 0 = 0) :
    mixedCanonicalSample v.val = mixedPermuteSample (mixedPostExchangePermutation v.val)
      (mixedSwapSample (mixedPreExchangeSample v.val)) := by
  calc
    mixedCanonicalSample v.val = binarySorted (mixedCornerSample v.val) :=
      mixedCanonicalSample_eq_sorted _
    _ = binarySorted (mixedPreExchangeSample v.val) := by
      rw [mixedPreExchangeSample, mixedPermuteSample_eq_comp, binarySorted_comp]
    _ = binarySorted (mixedSwapSample (mixedPreExchangeSample v.val)) := by
      exact (binarySorted_comp (mixedPreExchangeSample v.val) (mixedExchangePermutation s)).symm
    _ = _ := by
      rw [mixedPermuteSample_eq_comp]
      exact binarySorted_tail _ (mixedPreExchangeSample_one v h0)

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedRootExchangeCorrection
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) :=
  (W.rationalDilation (((s + 3 : ℕ) : ℚ)⁻¹)).mixedTensorExchangeCorrection ((s + 3) ^ (s + 2)) (W.divisionMixedExchangeCorrection (s + 3) G)

theorem mixedRootExchangeCorrection_norm {N : ℕ} [NeZero N]
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (π : Fin (s + 3) → Fin 2) (a b : Fin W.mixedIntegrationRoot.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.mixedRootExchangeCorrection G π a b (fun k => ((x k).val : ℤ))‖ ≤ (W.outputDim : ℝ) ^ (2 * ((s + 3) ^ (s + 2))) := by
  have hH (π : Fin (s + 3) → Fin 2) (i j : Fin W.outputDim) (x : Fin 2 → ZMod N) :
      ‖W.divisionMixedExchangeCorrection (s + 3) G π i j (fun k => ((x k).val : ℤ))‖ ≤ (W.outputDim : ℝ) ^ 2 := by
    simpa only [mul_one] using W.divisionMixedExchangeCorrection_norm (s + 3) G hG π i j x
  simpa only [mixedRootExchangeCorrection, ← pow_mul] using
    (W.rationalDilation (((s + 3 : ℕ) : ℚ)⁻¹)).mixedTensorExchangeCorrection_norm ((s + 3) ^ (s + 2))
      (W.divisionMixedExchangeCorrection (s + 3) G) hH π a b x

theorem mixedRootExchangeCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (π : Fin (s + 3) → Fin 2) (a b : Fin W.mixedIntegrationRoot.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedIntegrationRoot.eval a (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.mixedIntegrationRoot.eval b
            (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        W.mixedRootExchangeCorrection G π a b (fun k => ((x k).val : ℤ))‖) ≤
      (W.outputDim : ℝ) ^ (2 * ((s + 3) ^ (s + 2))) *
        ((((s + 3) ^ (s + 2) : ℕ) : ℝ) *
          (((s + 3 : ℕ) : ℝ) ^ 2 * (W.outputDim : ℝ) ^ 2 * ε)) := by
  exact W.dilationTensorMixedExchangeCorrection_mean_error
    (s + 3) ((s + 3) ^ (s + 2)) G hG herr π a b

theorem exists_mixedRootExchangeCorrection_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p), 0 ≤ q →
      ∀ G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ π i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (G π i j))) →
      ∀ π a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + q + C) ^ C)
        (W.mixedRootExchangeCorrection G π a b)) := by
  obtain ⟨A, _, hdivision⟩ := exists_divisionMixedExchangeCorrection_expansion s (s + 3)
  obtain ⟨B, _, htensor⟩ := exists_mixedTensorExchangeCorrection_expansion s ((s + 3) ^ (s + 2))
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q W hq G hG π a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  obtain ⟨E⟩ := htensor (W.rationalDilation (((s + 3 : ℕ) : ℚ)⁻¹)) (by positivity : 0 ≤ (p + q + A) ^ A)
    (W.divisionMixedExchangeCorrection (s + 3) G) (hdivision W hq G hG) π a b
  have hcost : ((p + q + A) ^ A + B) ^ B ≤ (p + q + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget (p + q) (add_nonneg hp hq)
  exact ⟨E.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

def mixedCornerCount (s : ℕ) : ℕ := 2 ^ (s + 3) - 1

theorem mixedNonconstantCorner_card_eq (s : ℕ) :
    Fintype.card (MixedNonconstantCorner s) = mixedCornerCount s := mixedNonconstantCorner_card s

namespace NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedRawCornerFactor (a b : MixedNonconstantCorner s → Fin W.outputDim)
    (v : MixedNonconstantCorner s) (x : Fin 2 → ℤ) : ℂ :=
  W.eval (a v) (mixedDiagonalCorner v.val x) *
    star (W.eval (b v) (mixedSampledInput (mixedCanonicalSample v.val) x))

theorem mixedRawCornerFactor_norm (a b : MixedNonconstantCorner s → Fin W.outputDim)
    (v : MixedNonconstantCorner s) (x : Fin 2 → ℤ) : ‖W.mixedRawCornerFactor a b v x‖ ≤ 1 := by
  rw [mixedRawCornerFactor, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

noncomputable def mixedCornerExchangeFactor
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a b : MixedNonconstantCorner s → Fin W.outputDim)
    (v : MixedNonconstantCorner s) (x : Fin 2 → ℤ) : ℂ :=
  if v.val 0 = 1 then W.mixedRawCornerFactor a b v x else
    complexCrossContraction
      (W.eval (a v) (mixedDiagonalCorner v.val x))
      (W.eval (b v) (mixedSampledInput (mixedCanonicalSample v.val) x))
      (fun i => W.eval i (mixedSampledInput (mixedPreExchangeSample v.val) x))
      (fun j => W.eval j (mixedSampledInput (mixedSwapSample (mixedPreExchangeSample v.val)) x))
      (fun i j => G (mixedPreExchangeSample v.val) i j x)

theorem mixedCornerExchangeFactor_norm {N : ℕ} [NeZero N] {B : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hB : 1 ≤ B)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (a b : MixedNonconstantCorner s → Fin W.outputDim) (v : MixedNonconstantCorner s)
    (x : Fin 2 → ZMod N) :
    ‖W.mixedCornerExchangeFactor G a b v (fun k => ((x k).val : ℤ))‖ ≤
      (W.outputDim : ℝ) ^ 2 * B := by
  have hd : (1 : ℝ) ≤ W.outputDim := by exact_mod_cast W.output_pos
  have hd2 : (1 : ℝ) ≤ (W.outputDim : ℝ) ^ 2 := by nlinarith
  have hQ : 1 ≤ (W.outputDim : ℝ) ^ 2 * B :=
    hB.trans (le_mul_of_one_le_left (zero_le_one.trans hB) hd2)
  by_cases hv : v.val 0 = 1
  · rw [mixedCornerExchangeFactor, ite_eq_left hv]
    exact (W.mixedRawCornerFactor_norm a b v _).trans hQ
  · rw [mixedCornerExchangeFactor, ite_eq_right hv]
    have h := norm_complexCrossContraction_le_card
      (W.eval (a v) (mixedDiagonalCorner v.val (fun k => ((x k).val : ℤ))))
      (W.eval (b v) (mixedSampledInput (mixedCanonicalSample v.val) (fun k => ((x k).val : ℤ))))
      (fun i => W.eval i (mixedSampledInput (mixedPreExchangeSample v.val) (fun k => ((x k).val : ℤ))))
      (fun j => W.eval j (mixedSampledInput (mixedSwapSample (mixedPreExchangeSample v.val))
        (fun k => ((x k).val : ℤ))))
      (fun i j => G (mixedPreExchangeSample v.val) i j (fun k => ((x k).val : ℤ)))
      (W.norm_eval _ _) (W.norm_eval _ _) (fun _ => W.norm_eval _ _) (fun _ => W.norm_eval _ _)
      (fun i j => hG _ i j x)
    convert h using 1; first | rfl | simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two]

theorem mixedCornerExchangeFactor_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hε : 0 ≤ ε)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a b : MixedNonconstantCorner s → Fin W.outputDim) (v : MixedNonconstantCorner s) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedRawCornerFactor a b v (fun k => ((x k).val : ℤ)) -
        W.mixedCornerExchangeFactor G a b v (fun k => ((x k).val : ℤ))‖) ≤
      (W.outputDim : ℝ) ^ 2 * ε := by
  by_cases hv : v.val 0 = 1
  · simpa [mixedCornerExchangeFactor, hv] using mul_nonneg (sq_nonneg (W.outputDim : ℝ)) hε
  · simp only [mixedCornerExchangeFactor, ite_eq_right hv, mixedRawCornerFactor]
    have h := mean_complexCrossContraction_error_le_card
      (fun x : Fin 2 → ZMod N => W.eval (a v) (mixedDiagonalCorner v.val (fun k => ((x k).val : ℤ))))
      (fun x => W.eval (b v) (mixedSampledInput (mixedCanonicalSample v.val) (fun k => ((x k).val : ℤ))))
      (fun i x => W.eval i (mixedSampledInput (mixedPreExchangeSample v.val) (fun k => ((x k).val : ℤ))))
      (fun j x => W.eval j (mixedSampledInput (mixedSwapSample (mixedPreExchangeSample v.val))
        (fun k => ((x k).val : ℤ))))
      (fun i j x => G (mixedPreExchangeSample v.val) i j (fun k => ((x k).val : ℤ)))
      (fun _ => W.norm_eval _ _) (fun _ => W.norm_eval _ _)
      (fun _ => W.unit_eval _) (fun _ => W.unit_eval _)
      (fun _ _ => W.norm_eval _ _) (fun _ _ => W.norm_eval _ _) (herr (mixedPreExchangeSample v.val))
    convert h using 1; first | rfl | simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two]

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedCanonicalTensor (a : MixedNonconstantCorner s → Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  star (∏ v, W.eval (a v) (mixedSampledInput (mixedCanonicalSample v.val) x))

theorem mixedCanonicalTensor_norm (a : MixedNonconstantCorner s → Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.mixedCanonicalTensor a x‖ ≤ 1 := by
  rw [mixedCanonicalTensor, norm_star, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => W.norm_eval _ _)

theorem mixedCanonicalTensor_unit (x : Fin 2 → ℤ) :
    ∑ a : MixedNonconstantCorner s → Fin W.outputDim, ‖W.mixedCanonicalTensor a x‖ ^ 2 = 1 := by
  simp only [mixedCanonicalTensor, norm_star, norm_prod, ← Finset.prod_pow]
  calc
    _ = ∏ v : MixedNonconstantCorner s, ∑ a : Fin W.outputDim,
        ‖W.eval a (mixedSampledInput (mixedCanonicalSample v.val) x)‖ ^ 2 := (Fintype.prod_sum _).symm
    _ = 1 := by simp only [W.unit_eval, Finset.prod_const_one]

theorem mixedNonconstantTensor_cross_symmetric
    (a b : MixedNonconstantCorner s → Fin W.outputDim) (x : Fin 2 → ℤ) :
    W.mixedNonconstantTensor a x * star (W.mixedCanonicalTensor b x) =
      star (∏ v, W.mixedRawCornerFactor a b v x) := by
  simp only [mixedNonconstantTensor, mixedCanonicalTensor, mixedRawCornerFactor,
    Finset.prod_mul_distrib, star_prod, star_mul, star_star]
  ring

noncomputable def mixedCornerExchangeProduct
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a b : MixedNonconstantCorner s → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  star (∏ v, W.mixedCornerExchangeFactor G a b v x)

theorem mixedCornerExchangeProduct_norm {N : ℕ} [NeZero N] {B : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hB : 1 ≤ B)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (a b : MixedNonconstantCorner s → Fin W.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.mixedCornerExchangeProduct G a b (fun k => ((x k).val : ℤ))‖ ≤
      ((W.outputDim : ℝ) ^ 2 * B) ^ (mixedCornerCount s) := by
  rw [mixedCornerExchangeProduct, norm_star, norm_prod]
  calc
    _ ≤ ∏ _ : MixedNonconstantCorner s, (W.outputDim : ℝ) ^ 2 * B :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun v _ => W.mixedCornerExchangeFactor_norm G hB hG a b v x)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, mixedNonconstantCorner_card_eq]

theorem mixedCornerExchangeProduct_mean_error {N : ℕ} [NeZero N] {B ε : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hB : 1 ≤ B) (hε : 0 ≤ ε)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a b : MixedNonconstantCorner s → Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedNonconstantTensor a (fun k => ((x k).val : ℤ)) *
          star (W.mixedCanonicalTensor b (fun k => ((x k).val : ℤ))) -
        W.mixedCornerExchangeProduct G a b (fun k => ((x k).val : ℤ))‖) ≤
      ((W.outputDim : ℝ) ^ 2 * B) ^ (mixedCornerCount s) * ((mixedCornerCount s) * ((W.outputDim : ℝ) ^ 2 * ε)) := by
  have hd : (1 : ℝ) ≤ W.outputDim := by exact_mod_cast W.output_pos
  have hd2 : (1 : ℝ) ≤ (W.outputDim : ℝ) ^ 2 := by nlinarith
  have hQ : 1 ≤ (W.outputDim : ℝ) ^ 2 * B :=
    hB.trans (le_mul_of_one_le_left (zero_le_one.trans hB) hd2)
  have h := mean_prod_error_le
    (fun v (x : Fin 2 → ZMod N) => W.mixedRawCornerFactor a b v (fun k => ((x k).val : ℤ)))
    (fun v (x : Fin 2 → ZMod N) => W.mixedCornerExchangeFactor G a b v (fun k => ((x k).val : ℤ))) hQ
    (fun v x => (W.mixedRawCornerFactor_norm a b v _).trans hQ)
    (fun v x => W.mixedCornerExchangeFactor_norm G hB hG a b v x)
    (fun v => W.mixedCornerExchangeFactor_mean_error G hε herr a b v)
  simpa only [W.mixedNonconstantTensor_cross_symmetric, mixedCornerExchangeProduct,
    ← star_sub, norm_star, mixedNonconstantCorner_card_eq] using h

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_corner_exchange_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)
      (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ),
      0 ≤ q → 0 ≤ r →
      (∀ π i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (G π i j))) →
      (∀ (e : Equiv.Perm (Fin (s + 2))) (π : Fin (s + 3) → Fin 2), NativeIntegerVectorEquivalence (s + 2) r
        (fun i (x : Fin 2 → ℤ) => W.eval i (mixedSampledInput π x))
        (fun i x => W.eval i (mixedSampledInput (mixedPermuteSample e π) x))) →
      ∀ a b v, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((q + r + C) ^ C)
        (W.mixedCornerExchangeFactor G a b v)) := by
  obtain ⟨A, _, hcontract⟩ := exists_native_cross_contraction
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + (X + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro p q r W G hq hr hG hperm a b v
  let t := q + r
  have ht : 0 ≤ t := add_nonneg hq hr
  have hqt : q ≤ t := by dsimp [t]; linarith
  have hrt : r ≤ t := by dsimp [t]; linarith
  have hsum : t + (t + A) ^ A ≤ (q + r + C) ^ C := by
    simpa [X, t, Polynomial.eval₂_pow] using hbudget (q + r) (add_nonneg hq hr)
  have htC : t ≤ (q + r + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have hAC : (t + A) ^ A ≤ (q + r + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  by_cases hv : v.val 0 = 1
  · have hcanon := mixedCanonicalSample_of_first_one v.val hv
    obtain ⟨F⟩ := ((hperm (mixedTailSortPermutation v.val)
      (mixedCornerSample v.val)).mono hrt).expansion (a v) (b v)
    have heq : (fun x => W.eval (a v) (mixedSampledInput (mixedCornerSample v.val) x) *
        star (W.eval (b v) (mixedSampledInput
          (mixedPermuteSample (mixedTailSortPermutation v.val)
            (mixedCornerSample v.val)) x))) = W.mixedCornerExchangeFactor G a b v := by
      funext x
      simp only [mixedCornerExchangeFactor, ite_eq_left hv, mixedRawCornerFactor,
        mixedCornerSample_input, hcanon]
    exact ⟨heq ▸ F.mono htC⟩
  · have hv0 := binary_eq_zero_of_ne_one (v.val 0) hv
    have hcanon := mixedCanonicalSample_of_first_zero v hv0
    have Eleft : NativeIntegerVectorEquivalence (s + 2) t
        (fun i (x : Fin 2 → ℤ) => W.eval i (mixedDiagonalCorner v.val x))
        (fun i x => W.eval i (mixedSampledInput (mixedPreExchangeSample v.val) x)) := by
      simpa only [mixedCornerSample_input, mixedPreExchangeSample] using
        (hperm (mixedHeadPermutation v.val) (mixedCornerSample v.val)).mono hrt
    have Eright : NativeIntegerVectorEquivalence (s + 2) t
        (fun i (x : Fin 2 → ℤ) => W.eval i (mixedSampledInput (mixedCanonicalSample v.val) x))
        (fun i x => W.eval i (mixedSampledInput (mixedSwapSample (mixedPreExchangeSample v.val)) x)) := by
      rw [hcanon]
      exact ((hperm (mixedPostExchangePermutation v.val)
        (mixedSwapSample (mixedPreExchangeSample v.val))).mono hrt).symm
    have H := hcontract (fun i j x => G (mixedPreExchangeSample v.val) i j x) ht Eleft Eright
      (fun i j => ⟨(Classical.choice (hG _ i j)).mono hqt⟩) (a v) (b v)
    have heq : (fun x => complexCrossContraction
        (W.eval (a v) (mixedDiagonalCorner v.val x))
        (W.eval (b v) (mixedSampledInput (mixedCanonicalSample v.val) x))
        (fun i => W.eval i (mixedSampledInput (mixedPreExchangeSample v.val) x))
        (fun j => W.eval j (mixedSampledInput (mixedSwapSample (mixedPreExchangeSample v.val)) x))
        (fun i j => G (mixedPreExchangeSample v.val) i j x)) = W.mixedCornerExchangeFactor G a b v := by
      funext x
      simp only [mixedCornerExchangeFactor, ite_eq_right hv]
    exact ⟨heq ▸ (Classical.choice H).mono hAC⟩

theorem exists_mixed_corner_product_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)
      (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ),
      0 ≤ q → 0 ≤ r →
      (∀ π i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (G π i j))) →
      (∀ (e : Equiv.Perm (Fin (s + 2))) (π : Fin (s + 3) → Fin 2), NativeIntegerVectorEquivalence (s + 2) r
        (fun i (x : Fin 2 → ℤ) => W.eval i (mixedSampledInput π x))
        (fun i x => W.eval i (mixedSampledInput (mixedPermuteSample e π) x))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((q + r + C) ^ C)
        (W.mixedCornerExchangeProduct G a b)) := by
  obtain ⟨A, _, hfactor⟩ := exists_mixed_corner_exchange_expansion s
  obtain ⟨B, _, hprod⟩ := NativeIntegerExpansion.exists_fin_prod_budget (mixedCornerCount s)
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q r W G hq hr hG hperm a b
  let e : Fin (mixedCornerCount s) ≃ MixedNonconstantCorner s := (Fintype.equivFinOfCardEq (mixedNonconstantCorner_card_eq s)).symm
  obtain ⟨F⟩ := hprod (fun k => W.mixedCornerExchangeFactor G a b (e k))
    (by positivity : 0 ≤ (q + r + A) ^ A)
    (fun k => hfactor W G hq hr hG hperm a b (e k))
  have hcost : ((q + r + A) ^ A + B) ^ B ≤ (q + r + C) ^ C := by
    simpa [X, T, Polynomial.eval₂_pow] using hbudget (q + r) (add_nonneg hq hr)
  have heq : (fun x => star (∏ k : Fin (mixedCornerCount s), W.mixedCornerExchangeFactor G a b (e k) x)) =
      W.mixedCornerExchangeProduct G a b := by
    funext x
    exact congrArg star (e.prod_comp (fun v => W.mixedCornerExchangeFactor G a b v x))
  exact ⟨heq ▸ F.conjugate.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedPermutedDiagonalCorrection
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim) (b : MixedNonconstantCorner s → Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  ∑ c : MixedNonconstantCorner s → Fin W.outputDim,
    (W.mixedDiagonalDerivative a x * star (W.mixedNonconstantTensor c x)) *
      W.mixedCornerExchangeProduct G c b x

theorem mixedPermutedDiagonalCorrection_norm {N : ℕ} [NeZero N] {B : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) (hB : 1 ≤ B)
    (hG : ∀ π a b (x : Fin 2 → ZMod N), ‖G π a b (fun z => ((x z).val : ℤ))‖ ≤ B)
    (a : Fin W.outputDim × Fin W.outputDim) (b : MixedNonconstantCorner s → Fin W.outputDim)
    (x : Fin 2 → ZMod N) :
    ‖W.mixedPermutedDiagonalCorrection G a b (fun z => ((x z).val : ℤ))‖ ≤
      (W.outputDim : ℝ) ^ (mixedCornerCount s) * ((W.outputDim : ℝ) ^ 2 * B) ^ (mixedCornerCount s) := by
  unfold mixedPermutedDiagonalCorrection
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _ : MixedNonconstantCorner s → Fin W.outputDim, ((W.outputDim : ℝ) ^ 2 * B) ^ (mixedCornerCount s) := by
      apply Finset.sum_le_sum
      intro c _
      rw [norm_mul]
      apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans
        (W.mixedCornerExchangeProduct_norm G hB hG c b x)
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (W.mixedDiagonalDerivative_norm _ _)).trans (W.mixedNonconstantTensor_norm _ _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        mixedNonconstantCorner_card_eq, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]

theorem mixedPermutedDiagonalCorrection_mean_error {N : ℕ} [NeZero N] {B ε : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) (hB : 1 ≤ B)
    (hG : ∀ π a b (x : Fin 2 → ZMod N), ‖G π a b (fun z => ((x z).val : ℤ))‖ ≤ B)
    (hε : 0 ≤ ε)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a : Fin W.outputDim × Fin W.outputDim) (b : MixedNonconstantCorner s → Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
        W.mixedPermutedDiagonalCorrection G a b (fun z => ((x z).val : ℤ))‖) ≤
      (W.outputDim : ℝ) ^ (mixedCornerCount s) * (((W.outputDim : ℝ) ^ 2 * B) ^ (mixedCornerCount s) * ((mixedCornerCount s) * ((W.outputDim : ℝ) ^ 2 * ε))) := by
  have hid (x : Fin 2 → ℤ) :
      W.mixedDiagonalDerivative a x * star (W.mixedCanonicalTensor b x) =
        ∑ c : MixedNonconstantCorner s → Fin W.outputDim,
          (W.mixedDiagonalDerivative a x * star (W.mixedNonconstantTensor c x)) *
            (W.mixedNonconstantTensor c x * star (W.mixedCanonicalTensor b x)) := by
    calc
      _ = ∑ c, ((W.mixedDiagonalDerivative a x * star (W.mixedCanonicalTensor b x)) *
          star (W.mixedNonconstantTensor c x)) * W.mixedNonconstantTensor c x :=
        complex_unit_vector_resolution _ (W.mixedNonconstantTensor_unit x) _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro c _
        ring
  have hpoint (x : Fin 2 → ZMod N) :
      ‖W.mixedDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
        W.mixedPermutedDiagonalCorrection G a b (fun z => ((x z).val : ℤ))‖ ≤
      ∑ c : MixedNonconstantCorner s → Fin W.outputDim,
        ‖W.mixedNonconstantTensor c (fun z => ((x z).val : ℤ)) *
            star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
          W.mixedCornerExchangeProduct G c b (fun z => ((x z).val : ℤ))‖ := by
    rw [hid, mixedPermutedDiagonalCorrection, ← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro c _
    rw [← mul_sub, norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (W.mixedDiagonalDerivative_norm _ _)).trans (W.mixedNonconstantTensor_norm _ _)
  calc
    _ ≤ 𝔼 x : Fin 2 → ZMod N, ∑ c : MixedNonconstantCorner s → Fin W.outputDim,
        ‖W.mixedNonconstantTensor c (fun z => ((x z).val : ℤ)) *
            star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
          W.mixedCornerExchangeProduct G c b (fun z => ((x z).val : ℤ))‖ :=
      Finset.expect_le_expect (fun x _ => hpoint x)
    _ = ∑ c : MixedNonconstantCorner s → Fin W.outputDim, 𝔼 x : Fin 2 → ZMod N,
        ‖W.mixedNonconstantTensor c (fun z => ((x z).val : ℤ)) *
            star (W.mixedCanonicalTensor b (fun z => ((x z).val : ℤ))) -
          W.mixedCornerExchangeProduct G c b (fun z => ((x z).val : ℤ))‖ :=
      Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _ : MixedNonconstantCorner s → Fin W.outputDim,
        ((W.outputDim : ℝ) ^ 2 * B) ^ (mixedCornerCount s) * ((mixedCornerCount s) * ((W.outputDim : ℝ) ^ 2 * ε)) :=
      Finset.sum_le_sum (fun c _ => W.mixedCornerExchangeProduct_mean_error G hB hε hG herr c b)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        mixedNonconstantCorner_card_eq, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]

theorem exists_mixed_permuted_diagonal_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)
      (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ), 0 ≤ q → 0 ≤ r →
      (∀ π i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (G π i j))) →
      (∀ (e : Equiv.Perm (Fin (s + 2))) (π : Fin (s + 3) → Fin 2), NativeIntegerVectorEquivalence (s + 2) r
        (fun i (x : Fin 2 → ℤ) => W.eval i (mixedSampledInput π x))
        (fun i x => W.eval i (mixedSampledInput (mixedPermuteSample e π) x))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + q + r + C) ^ C)
        (W.mixedPermutedDiagonalCorrection G a b)) := by
  obtain ⟨A, _, hderivative⟩ := exists_mixed_diagonal_derivative_equivalence s
  obtain ⟨B, _, hseven⟩ := exists_mixed_corner_product_expansion s
  obtain ⟨D, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C D) ^ D + Polynomial.C (mixedCornerCount s) * X)
  refine ⟨C, hC, ?_⟩
  intro p q r W G hq hr hG hperm a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let t := (p + q + r + A) ^ A + (p + q + r + B) ^ B
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hAt : (p + A) ^ A ≤ t := by
    apply le_trans _ (le_add_of_nonneg_right (by positivity))
    exact pow_le_pow_left₀ (by positivity) (by linarith) A
  have hBt : (q + r + B) ^ B ≤ t := by
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hterm (c : MixedNonconstantCorner s → Fin W.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((t + D) ^ D)
        (fun x => (W.mixedDiagonalDerivative a x * star (W.mixedNonconstantTensor c x)) *
          W.mixedCornerExchangeProduct G c b x)) := by
    exact hmul ht (Classical.choice (((hderivative W).mono hAt).expansion a c))
      ((Classical.choice (hseven W G hq hr hG hperm c b)).mono hBt)
  have hdim : (Fintype.card (MixedNonconstantCorner s → Fin W.outputDim) : ℝ) ≤ Real.exp ((mixedCornerCount s) * p) := by
    simp only [Fintype.card_fun, mixedNonconstantCorner_card_eq, Fintype.card_fin, Nat.cast_pow]
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) W.output_bound (mixedCornerCount s)).trans_eq
      (Real.exp_nat_mul p (mixedCornerCount s)).symm
  have hcoeff : (∑ _ : MixedNonconstantCorner s → Fin W.outputDim, ‖(1 : ℂ)‖) ≤ Real.exp ((mixedCornerCount s) * p) := by
    simpa using hdim
  have H := NativeIntegerExpansion.weightedSum (fun c => Classical.choice (hterm c))
    (fun _ => 1) (by positivity : 0 ≤ (mixedCornerCount s) * p) hdim hcoeff
  have hcost : (t + D) ^ D + (mixedCornerCount s) * p ≤ (p + q + r + C) ^ C := by
    have hb : (t + D) ^ D + (mixedCornerCount s) * (p + q + r) ≤ (p + q + r + C) ^ C := by
      simpa [X, T, t, Polynomial.eval₂_pow] using hbudget (p + q + r) (by positivity)
    have hmono : (mixedCornerCount s : ℝ) * p ≤ (mixedCornerCount s : ℝ) * (p + q + r) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    linarith
  refine ⟨?_⟩
  change NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + q + r + C) ^ C)
    (fun x => ∑ c : MixedNonconstantCorner s → Fin W.outputDim,
      (W.mixedDiagonalDerivative a x * star (W.mixedNonconstantTensor c x)) *
        W.mixedCornerExchangeProduct G c b x)
  simpa only [one_mul] using H.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedRootCornerCorrection
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) :=
  W.mixedIntegrationRoot.mixedPermutedDiagonalCorrection (W.mixedRootExchangeCorrection G)

theorem mixedRootCornerCorrection_norm {N : ℕ} [NeZero N]
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (a : Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim)
    (b : MixedNonconstantCorner s → Fin W.mixedIntegrationRoot.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.mixedRootCornerCorrection G a b (fun k => ((x k).val : ℤ))‖ ≤
      (W.mixedIntegrationRoot.outputDim : ℝ) ^ mixedCornerCount s *
        ((W.mixedIntegrationRoot.outputDim : ℝ) ^ 2 *
          (W.outputDim : ℝ) ^ (2 * ((s + 3) ^ (s + 2)))) ^ mixedCornerCount s := by
  have hd : (1 : ℝ) ≤ W.outputDim := by exact_mod_cast W.output_pos
  have hB : 1 ≤ (W.outputDim : ℝ) ^ (2 * ((s + 3) ^ (s + 2))) := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hd (2 * ((s + 3) ^ (s + 2)))
  exact W.mixedIntegrationRoot.mixedPermutedDiagonalCorrection_norm
    (W.mixedRootExchangeCorrection G) hB (W.mixedRootExchangeCorrection_norm G hG) a b x

theorem mixedRootCornerCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hε : 0 ≤ ε)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a : Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim)
    (b : MixedNonconstantCorner s → Fin W.mixedIntegrationRoot.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedIntegrationRoot.mixedDiagonalDerivative a (fun k => ((x k).val : ℤ)) *
          star (W.mixedIntegrationRoot.mixedCanonicalTensor b (fun k => ((x k).val : ℤ))) -
        W.mixedRootCornerCorrection G a b (fun k => ((x k).val : ℤ))‖) ≤
      (W.mixedIntegrationRoot.outputDim : ℝ) ^ mixedCornerCount s *
        (((W.mixedIntegrationRoot.outputDim : ℝ) ^ 2 *
            (W.outputDim : ℝ) ^ (2 * ((s + 3) ^ (s + 2)))) ^ mixedCornerCount s *
          ((mixedCornerCount s : ℝ) * ((W.mixedIntegrationRoot.outputDim : ℝ) ^ 2 *
            ((W.outputDim : ℝ) ^ (2 * ((s + 3) ^ (s + 2))) *
              ((((s + 3) ^ (s + 2) : ℕ) : ℝ) *
                (((s + 3 : ℕ) : ℝ) ^ 2 * (W.outputDim : ℝ) ^ 2 * ε)))))) := by
  have hd : (1 : ℝ) ≤ W.outputDim := by exact_mod_cast W.output_pos
  have hB : 1 ≤ (W.outputDim : ℝ) ^ (2 * ((s + 3) ^ (s + 2))) := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hd (2 * ((s + 3) ^ (s + 2)))
  exact W.mixedIntegrationRoot.mixedPermutedDiagonalCorrection_mean_error
    (W.mixedRootExchangeCorrection G) hB (W.mixedRootExchangeCorrection_norm G hG)
    (by positivity) (W.mixedRootExchangeCorrection_mean_error G hG herr) a b

theorem exists_mixedRootCornerCorrection_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p), 0 ≤ q →
      (∀ (a : ReplicatedPermutation (mixedCorrelationDegree (s + 2))) i x,
        W.eval i (fun j => x ((replicatedPermutation (mixedCorrelationDegree (s + 2)) a).symm j)) = W.eval i x) →
      ∀ G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ π i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (G π i j))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + q + C) ^ C)
        (W.mixedRootCornerCorrection G a b)) := by
  obtain ⟨A, _, hroot⟩ := exists_mixedRootExchangeCorrection_expansion s
  obtain ⟨B, _, hperm⟩ := exists_mixed_root_last_slots_equivalence s
  obtain ⟨D, _, hdiagonal⟩ := exists_mixed_permuted_diagonal_expansion s
  let n := (s + 3) ^ (s + 2)
  let X : Polynomial ℕ := Polynomial.X
  let T := Polynomial.C (n + 1) * (X + 1) + (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro p q W hq hsymm G hG a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  obtain ⟨E⟩ := hdiagonal W.mixedIntegrationRoot (W.mixedRootExchangeCorrection G)
    (by positivity : 0 ≤ (p + q + A) ^ A) (by positivity : 0 ≤ (p + B) ^ B)
    (hroot W hq G hG) (hperm W hsymm) a b
  have hcost : (tensorPowerBudget n p + (p + q + A) ^ A + (p + B) ^ B + D) ^ D ≤
      (p + q + C) ^ C := by
    have hmono : (p + B) ^ B ≤ (p + q + B) ^ B :=
      pow_le_pow_left₀ (by positivity) (by linarith) B
    have hbase : tensorPowerBudget n p ≤ (n + 1 : ℝ) * (p + q + 1) := by
      unfold tensorPowerBudget
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hbound : ((n + 1 : ℝ) * (p + q + 1) + (p + q + A) ^ A + (p + q + B) ^ B + D) ^ D ≤
        (p + q + C) ^ C := by
      simpa [X, T, Polynomial.eval₂_pow] using hbudget (p + q) (add_nonneg hp hq)
    apply le_trans _ hbound
    apply pow_le_pow_left₀ (by unfold tensorPowerBudget; positivity)
    linarith
  exact ⟨E.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

def mixedRootTensorExponent (s : ℕ) : ℕ := (s + 3) ^ (s + 2)

def mixedRootCornerExponent (s : ℕ) : ℕ :=
  5 * mixedRootTensorExponent s * mixedCornerCount s + 4 * mixedRootTensorExponent s + 2

def mixedRootCornerCoefficient (s : ℕ) : ℕ :=
  mixedCornerCount s * mixedRootTensorExponent s * (s + 3) ^ 2

theorem root_corner_loss_identity (D : ℝ) (n m q : ℕ) (ε : ℝ) :
    (D ^ n) ^ m * (((D ^ n) ^ 2 * D ^ (2 * n)) ^ m *
      ((m : ℝ) * ((D ^ n) ^ 2 * (D ^ (2 * n) *
        ((n : ℝ) * ((q : ℝ) ^ 2 * D ^ 2 * ε)))))) =
      ((m * n * q ^ 2 : ℕ) : ℝ) * D ^ (5 * n * m + 4 * n + 2) * ε := by
  have hp0 : (D ^ n) ^ m = D ^ (n * m) := (pow_mul D n m).symm
  have hp1 : ((D ^ n) ^ 2 * D ^ (2 * n)) ^ m = D ^ ((n * 2 + 2 * n) * m) := by
    simp only [← pow_mul, ← pow_add]
  have hp2 : (D ^ n) ^ 2 = D ^ (n * 2) := (pow_mul D n 2).symm
  have hp : D ^ (n * m) * D ^ ((n * 2 + 2 * n) * m) * D ^ (n * 2) * D ^ (2 * n) * D ^ 2 =
      D ^ (5 * n * m + 4 * n + 2) := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    ring
  rw [hp0, hp1, hp2]
  calc
    _ = ((m : ℝ) * n * (q : ℝ) ^ 2) *
        (D ^ (n * m) * D ^ ((n * 2 + 2 * n) * m) * D ^ (n * 2) * D ^ (2 * n) * D ^ 2) * ε := by ring
    _ = _ := by rw [hp]; simp only [Nat.cast_mul, Nat.cast_pow]

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

theorem mixedIntegrationRoot_outputDim :
    W.mixedIntegrationRoot.outputDim = W.outputDim ^ mixedRootTensorExponent s := rfl

theorem mixedRootCornerCorrection_mean_error_power {N : ℕ} [NeZero N] {ε : ℝ}
    (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hε : 0 ≤ ε)
    (hG : ∀ π i j (x : Fin 2 → ZMod N), ‖G π i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (herr : ∀ π i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval i (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval j (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a : Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim)
    (b : MixedNonconstantCorner s → Fin W.mixedIntegrationRoot.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedIntegrationRoot.mixedDiagonalDerivative a (fun k => ((x k).val : ℤ)) *
          star (W.mixedIntegrationRoot.mixedCanonicalTensor b (fun k => ((x k).val : ℤ))) -
        W.mixedRootCornerCorrection G a b (fun k => ((x k).val : ℤ))‖) ≤
      (mixedRootCornerCoefficient s : ℝ) * (W.outputDim : ℝ) ^ mixedRootCornerExponent s * ε := by
  have H := W.mixedRootCornerCorrection_mean_error G hε hG herr a b
  apply H.trans_eq
  rw [W.mixedIntegrationRoot_outputDim, Nat.cast_pow]
  exact root_corner_loss_identity (W.outputDim : ℝ) (mixedRootTensorExponent s) (mixedCornerCount s) (s + 3) ε

end NativeMultidegreeNilcharacter
end Erdos3

end

end OAI
