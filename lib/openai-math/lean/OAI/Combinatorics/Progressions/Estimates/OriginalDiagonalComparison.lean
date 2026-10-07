/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.UnitVerticalCyclicDifference

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def originalDiagonalCorrection
    (F : (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) →
      (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) →
      (Fin 2 → ℤ) → ℂ)
    (a : Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim)
    (i : Fin W.outputDim) (c : Fin W.quadraticRoot.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  ∑ b : Fin 2 → Fin W.quadraticRoot.outputDim,
    (W.eval i x * star (tensorVector W.quadraticRoot.eval 2 b x)) * F a (b 0, b 1, c) x

theorem originalDiagonalCorrection_pointwise_error {N : ℕ} [NeZero N]
    (F : (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) →
      (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) →
      (Fin 2 → ℤ) → ℂ)
    (a : Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim)
    (i : Fin W.outputDim) (c : Fin W.quadraticRoot.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.quadraticRoot.cyclicDiagonalDerivative a x *
        (W.eval i (fun k => ((x k).val : ℤ)) * W.quadraticRoot.eval c (fun _ => ((x 0).val : ℤ))) -
      W.originalDiagonalCorrection F a i c (fun k => ((x k).val : ℤ))‖ ≤
      ∑ b : Fin 2 → Fin W.quadraticRoot.outputDim,
        ‖W.quadraticRoot.cyclicDiagonalDerivative a x *
            star (W.quadraticRoot.quadraticSquareTriple (b 0, b 1, c) (fun k => ((x k).val : ℤ))) -
          F a (b 0, b 1, c) (fun k => ((x k).val : ℤ))‖ := by
  let z : Fin 2 → ℤ := fun k => ((x k).val : ℤ)
  let R := W.quadraticRoot
  let D := R.cyclicDiagonalDerivative a x
  let T := tensorVector R.eval 2
  have hunit := tensorVector_unit R.eval R.unit_eval 2 z
  have hres := complex_unit_vector_resolution (fun b => T b z) hunit (W.eval i z)
  have hin : correlationInput (z 0) (z 1) = z := by funext k; fin_cases k <;> rfl
  have ht (b : Fin 2 → Fin R.outputDim) :
      star (R.quadraticSquareTriple (b 0, b 1, c) z) = T b z * R.eval c (fun _ => z 0) := by
    simp only [quadraticSquareTriple, star_star, hin, T, tensorVector, Fin.prod_univ_two]
  have heq : D * (W.eval i z * R.eval c (fun _ => z 0)) =
      ∑ b : Fin 2 → Fin R.outputDim,
        (W.eval i z * star (T b z)) * (D * star (R.quadraticSquareTriple (b 0, b 1, c) z)) := by
    calc
      _ = D * ((∑ b, (W.eval i z * star (T b z)) * T b z) * R.eval c (fun _ => z 0)) := by rw [← hres]
      _ = _ := by
        rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        rw [ht]
        ring
  change ‖D * (W.eval i z * R.eval c (fun _ => z 0)) - W.originalDiagonalCorrection F a i c z‖ ≤ _
  rw [heq, originalDiagonalCorrection, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b _
  rw [← mul_sub, norm_mul]
  have hc : ‖W.eval i z * star (T b z)‖ ≤ 1 := by
    rw [norm_mul, norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval i z)).trans
    dsimp [T, tensorVector]
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun k _ => R.norm_eval (b k) z)
  exact mul_le_of_le_one_left (norm_nonneg _) hc

theorem originalDiagonalCorrection_mean_error {N : ℕ} [NeZero N]
    (F : (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) →
      (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) →
      (Fin 2 → ℤ) → ℂ) {ε : ℝ}
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.quadraticRoot.cyclicDiagonalDerivative a x *
          star (W.quadraticRoot.quadraticSquareTriple b (fun k => ((x k).val : ℤ))) -
        F a b (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a : Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim)
    (i : Fin W.outputDim) (c : Fin W.quadraticRoot.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.quadraticRoot.cyclicDiagonalDerivative a x *
          (W.eval i (fun k => ((x k).val : ℤ)) * W.quadraticRoot.eval c (fun _ => ((x 0).val : ℤ))) -
        W.originalDiagonalCorrection F a i c (fun k => ((x k).val : ℤ))‖) ≤
      (W.quadraticRoot.outputDim : ℝ) ^ 2 * ε := by
  have hm := Finset.expect_le_expect (s := Finset.univ)
    (fun (x : Fin 2 → ZMod N) _ => W.originalDiagonalCorrection_pointwise_error F a i c x)
  rw [Finset.expect_sum_comm] at hm
  apply hm.trans
  calc
    _ ≤ ∑ _b : Fin 2 → Fin W.quadraticRoot.outputDim, ε :=
      Finset.sum_le_sum (fun b _ => herr a (b 0, b 1, c))
    _ = _ := by simp

theorem exists_originalDiagonalCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p), 0 ≤ q →
      ∀ F : (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) →
        (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) →
        (Fin 2 → ℤ) → ℂ,
      (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q (F a b))) →
      ∀ a i c, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + C) ^ C)
        (W.originalDiagonalCorrection F a i c)) := by
  obtain ⟨A, _, hequiv⟩ := exists_explicit_quadratic_root_equivalence
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + X + 3 * (X + 1) + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B + 6 * (X + 1))
  refine ⟨C, hC, ?_⟩
  intro p q W hq F hF a i c
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q
  let t := (v + A) ^ A + v + 3 * (v + 1) + 2
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hqr : q ≤ t := by
    have hh : 0 ≤ (v + A) ^ A := by positivity
    dsimp [v] at hh
    dsimp [t, v]
    linarith
  have hAr : (p + A) ^ A ≤ t := by
    apply (pow_le_pow_left₀ (by positivity) (show p + A ≤ v + A by dsimp [v]; linarith) A).trans
    dsimp [t]
    linarith
  have hcost : (t + B) ^ B + 6 * (v + 1) ≤ (p + q + C) ^ C := by
    simpa [T, X, t, v, Polynomial.eval₂_pow] using hbudget v hv
  have hterm (b : Fin 2 → Fin W.quadraticRoot.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((t + B) ^ B)
        (fun x => (W.eval i x * star (tensorVector W.quadraticRoot.eval 2 b x)) * F a (b 0, b 1, c) x)) :=
    hmul ht ((Classical.choice ((hequiv W).expansion i b)).mono hAr)
      ((Classical.choice (hF a (b 0, b 1, c))).mono hqr)
  have hcard : (Fintype.card (Fin 2 → Fin W.quadraticRoot.outputDim) : ℝ) ≤ Real.exp (6 * (v + 1)) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ Real.exp (tensorPowerBudget 2 p) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) W.quadraticRoot.output_bound _
      _ = Real.exp (2 * tensorPowerBudget 2 p) := by
        simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul (tensorPowerBudget 2 p) 2).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        norm_num [tensorPowerBudget]
        dsimp [v]
        linarith
  have hcoeff : (∑ _ : Fin 2 → Fin W.quadraticRoot.outputDim, ‖(1 : ℂ)‖) ≤ Real.exp (6 * (v + 1)) := by
    simpa using hcard
  have E := (NativeIntegerExpansion.weightedSum (fun b => Classical.choice (hterm b))
    (fun _ => (1 : ℂ)) (by positivity : 0 ≤ 6 * (v + 1)) hcard hcoeff).mono hcost
  refine ⟨?_⟩
  change NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + C) ^ C)
    (fun x => W.originalDiagonalCorrection F a i c x)
  simpa only [originalDiagonalCorrection, one_mul] using E

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
