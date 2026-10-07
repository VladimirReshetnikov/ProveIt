/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.DiagonalWrapComparison
import OAI.Combinatorics.Progressions.Polynomial.BoundedRootDegreeEquivalence

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_explicit_quadratic_root_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p),
      NativeIntegerVectorEquivalence 1 ((p + C) ^ C) W.eval
        (tensorVector ((W.rationalDilation (1 / 2)).tensorPower 2).eval 2) := by
  have hsum : (∑ i, mixedCorrelationDegree 1 i) = 2 := by decide
  have hpos : 1 ≤ ∑ i, mixedCorrelationDegree 1 i := by rw [hsum]; norm_num
  obtain ⟨A, _, hdilation⟩ := exists_dilation_degree_equivalence (mixedCorrelationDegree 1) hpos 2
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + 6 * (X + 1) + X + 2)
  refine ⟨C, hC, ?_⟩
  intro p W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hA : 0 ≤ (p + A) ^ A := by positivity
  have hbound : (p + A) ^ A + 6 * (p + 1) + p + 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hpr : p ≤ (p + C) ^ C := by linarith
  have hAr : (p + A) ^ A ≤ (p + C) ^ C := by linarith
  have hdimBound : 2 * tensorPowerBudget 2 p ≤ (p + C) ^ C := by
    norm_num [tensorPowerBudget]
    linarith
  let V := W.rationalDilation (1 / 2)
  let R := V.tensorPower 2
  have hleft (i : Fin W.outputDim) (x : Fin 2 → ℤ) :
      W.eval i x = integerDilationVector V.eval 2 i x :=
    (W.rationalDilation_eval_rescaled (1 / 2) 2 (by norm_num) i x).symm
  have hright (b : Fin 2 → Fin R.outputDim) (x : Fin 2 → ℤ) :
      tensorVector R.eval 2 b x =
        signedTensorVector V.eval ((2 : ℤ) ^ ∑ j, mixedCorrelationDegree 1 j)
          (rootTensorIndex W.outputDim 2 (∑ j, mixedCorrelationDegree 1 j) hpos b) x := by
    exact V.tensorPower_tensor_eval 2 (∑ j, mixedCorrelationDegree 1 j) hpos b x
  have hdim : (Fintype.card (Fin 2 → Fin R.outputDim) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ Real.exp (tensorPowerBudget 2 p) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) R.output_bound _
      _ = Real.exp (2 * tensorPowerBudget 2 p) := by
        simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul (tensorPowerBudget 2 p) 2).symm
      _ ≤ _ := Real.exp_le_exp.mpr hdimBound
  have E := (hdilation V).of_coordinate_maps W.eval (tensorVector R.eval 2) id
    (rootTensorIndex W.outputDim 2 (∑ j, mixedCorrelationDegree 1 j) hpos) hleft hright
    (by simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpr)) hdim hAr
  simpa only [hsum, Nat.reduceSub] using E

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

theorem norm_unit_vector_exchange_error {I : Type*} [Fintype I]
    (v : I → ℂ) (hv : ∑ i, ‖v i‖ ^ 2 = 1) (hcap : ∀ i, ‖v i‖ ≤ 1)
    (a : ℂ) (g : I → ℂ) :
    ‖a - ∑ i, v i * star (g i)‖ ≤ ∑ i, ‖star a * v i - g i‖ := by
  have hsum : (∑ i, v i * star (star a * v i)) = a := by
    calc
      _ = ∑ i, (a * star (v i)) * v i := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [star_mul, star_star]
        ring
      _ = a := (complex_unit_vector_resolution v hv a).symm
  have heq : a - ∑ i, v i * star (g i) = ∑ i, v i * star (star a * v i - g i) := by
    simp only [star_sub, mul_sub, Finset.sum_sub_distrib, hsum]
  rw [heq]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _) (hcap i)

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def quadraticSquareTriple (a : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  star ((W.eval a.1 (correlationInput (x 0) (x 1)) *
    W.eval a.2.1 (correlationInput (x 0) (x 1))) * W.eval a.2.2 (fun _ => x 0))

noncomputable def diagonalSquareCorrection
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  ∑ j, (W.quadraticDiagonalDerivative a x * star (W.quadraticMixedTriple (j, b.2) x)) *
    star (G b.1 j x)

theorem diagonalSquareCorrection_norm {N : ℕ} [NeZero N]
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ a b (x : Fin 2 → ZMod N), ‖G a b (fun z => ((x z).val : ℤ))‖ ≤ 1)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.diagonalSquareCorrection G a b (fun z => ((x z).val : ℤ))‖ ≤ W.outputDim := by
  unfold diagonalSquareCorrection
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _j : Fin W.outputDim, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        ((mul_le_of_le_one_left (norm_nonneg _) (W.quadraticDiagonalDerivative_norm a _)).trans
          (W.quadraticMixedTriple_norm _ _))).trans (hG b.1 j x)
    _ = _ := by simp

theorem diagonalSquareCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.antisymmetricKernel a b ((x 0).val : ℤ) ((x 1).val : ℤ) -
        G a b (fun z => ((x z).val : ℤ))‖) ≤ ε)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.quadraticDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))) -
        W.diagonalSquareCorrection G a b (fun z => ((x z).val : ℤ))‖) ≤ W.outputDim * ε := by
  have hpoint (x : Fin 2 → ZMod N) :
      ‖W.quadraticDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))) -
        W.diagonalSquareCorrection G a b (fun z => ((x z).val : ℤ))‖ ≤
      ∑ j, ‖W.antisymmetricKernel b.1 j ((x 0).val : ℤ) ((x 1).val : ℤ) -
        G b.1 j (fun z => ((x z).val : ℤ))‖ := by
    let z := fun i => ((x i).val : ℤ)
    let c := (W.quadraticDiagonalDerivative a z * W.eval b.2.1 (correlationInput (z 0) (z 1))) *
      W.eval b.2.2 (fun _ => z 0)
    have hc : ‖c‖ ≤ 1 := by
      simp only [c, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        ((mul_le_of_le_one_left (norm_nonneg _) (W.quadraticDiagonalDerivative_norm a z)).trans
          (W.norm_eval _ _))).trans (W.norm_eval _ _)
    have htarget : W.quadraticDiagonalDerivative a z * star (W.quadraticSquareTriple b z) =
        c * W.eval b.1 (correlationInput (z 0) (z 1)) := by
      simp only [quadraticSquareTriple, star_star, c]
      ring
    have hsum : W.diagonalSquareCorrection G a b z =
        c * ∑ j, W.eval j (correlationInput (z 1) (z 0)) * star (G b.1 j z) := by
      unfold diagonalSquareCorrection
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [quadraticMixedTriple, star_star, c]
      ring
    change ‖W.quadraticDiagonalDerivative a z * star (W.quadraticSquareTriple b z) -
      W.diagonalSquareCorrection G a b z‖ ≤ _
    rw [htarget, hsum, ← mul_sub, norm_mul]
    apply (mul_le_of_le_one_left (norm_nonneg _) hc).trans
    exact norm_unit_vector_exchange_error
      (fun j => W.eval j (correlationInput (z 1) (z 0))) (W.unit_eval _) (fun j => W.norm_eval j _)
      (W.eval b.1 (correlationInput (z 0) (z 1))) (fun j => G b.1 j z)
  calc
    _ ≤ 𝔼 x : Fin 2 → ZMod N,
        ∑ j, ‖W.antisymmetricKernel b.1 j ((x 0).val : ℤ) ((x 1).val : ℤ) -
          G b.1 j (fun z => ((x z).val : ℤ))‖ := Finset.expect_le_expect (fun x _ => hpoint x)
    _ = ∑ j, 𝔼 x : Fin 2 → ZMod N,
        ‖W.antisymmetricKernel b.1 j ((x 0).val : ℤ) ((x 1).val : ℤ) -
          G b.1 j (fun z => ((x z).val : ℤ))‖ := Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _j : Fin W.outputDim, ε := Finset.sum_le_sum (fun j _ => herr b.1 j)
    _ = _ := by simp

theorem exists_quadratic_diagonal_square_comparison :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q ε : ℝ} {N : ℕ} [NeZero N]
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
      (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ),
      0 ≤ q →
      (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q (G a b))) →
      (∀ a b (x : Fin 2 → ZMod N), ‖G a b (fun z => ((x z).val : ℤ))‖ ≤ 1) →
      (∀ a b, (𝔼 x : Fin 2 → ZMod N,
        ‖W.antisymmetricKernel a b ((x 0).val : ℤ) ((x 1).val : ℤ) -
          G a b (fun z => ((x z).val : ℤ))‖) ≤ ε) →
      ∃ F : (Fin W.outputDim × Fin W.outputDim) →
          (Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) → (Fin 2 → ℤ) → ℂ,
        (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
          ((p + q + C) ^ C) (F a b))) ∧
        (∀ a b (x : Fin 2 → ZMod N), ‖F a b (fun z => ((x z).val : ℤ))‖ ≤ W.outputDim) ∧
        (∀ a b, (𝔼 x : Fin 2 → ZMod N,
          ‖W.quadraticDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
              star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))) -
            F a b (fun z => ((x z).val : ℤ))‖) ≤ W.outputDim * ε) := by
  obtain ⟨A, _, hdiag⟩ := exists_quadratic_diagonal_derivative_equivalence
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + Polynomial.C A) ^ A + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C B) ^ B + X)
  refine ⟨C, hC, ?_⟩
  intro p q ε N _ W G hq hG hcap herr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q
  let r := (v + A) ^ A + v + 2
  have hv : 0 ≤ v := add_nonneg hp hq
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hqr : q ≤ r := by
    have : 0 ≤ (v + A) ^ A := by positivity
    dsimp [r, v]
    linarith
  have hAr : (p + A) ^ A ≤ r := by
    calc
      _ ≤ (v + A) ^ A := pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) A
      _ ≤ r := by dsimp [r]; linarith
  have hcost : (r + B) ^ B + p ≤ (p + q + C) ^ C := by
    have hh : (r + B) ^ B + v ≤ (p + q + C) ^ C := by
      simpa [X, R, r, v, Polynomial.eval₂_pow] using hbudget v hv
    dsimp [v] at hh
    linarith
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have hcoeff : (∑ _j : Fin W.outputDim, ‖(1 : ℂ)‖) ≤ Real.exp p := by simpa using hdim
  have hterm (a : Fin W.outputDim × Fin W.outputDim)
      (b : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) (j : Fin W.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((r + B) ^ B)
        (fun x => (W.quadraticDiagonalDerivative a x * star (W.quadraticMixedTriple (j, b.2) x)) *
          star (G b.1 j x))) :=
    hmul hr ((Classical.choice ((hdiag W).expansion a (j, b.2))).mono hAr)
      ((Classical.choice (hG b.1 j)).conjugate.mono hqr)
  refine ⟨W.diagonalSquareCorrection G, ?_, W.diagonalSquareCorrection_norm G hcap,
    W.diagonalSquareCorrection_mean_error G herr⟩
  intro a b
  have E := (NativeIntegerExpansion.weightedSum (fun j => Classical.choice (hterm a b j))
    (fun _ => (1 : ℂ)) hp hdim hcoeff).mono hcost
  change Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + C) ^ C)
    (fun x => ∑ j, (W.quadraticDiagonalDerivative a x * star (W.quadraticMixedTriple (j, b.2) x)) *
      star (G b.1 j x)))
  exact ⟨by simpa only [one_mul] using E⟩

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem norm_smoothed_branch_error (c w : ℝ) (hw : 0 ≤ w ∧ w ≤ 1)
    (a b u v : ℂ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖((1 - c : ℝ) : ℂ) * a + (c : ℂ) * b -
      (((1 - w : ℝ) : ℂ) * u + (w : ℂ) * v)‖ ≤
      ‖a - u‖ + ‖b - v‖ + 2 * |c - w| := by
  have heq : ((1 - c : ℝ) : ℂ) * a + (c : ℂ) * b -
      (((1 - w : ℝ) : ℂ) * u + (w : ℂ) * v) =
      (((1 - w : ℝ) : ℂ) * (a - u) + (w : ℂ) * (b - v)) +
        ((c - w : ℝ) : ℂ) * (b - a) := by push_cast; ring
  have hba : ‖b - a‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  rw [heq]
  calc
    _ ≤ ‖((1 - w : ℝ) : ℂ) * (a - u)‖ + ‖(w : ℂ) * (b - v)‖ +
        ‖((c - w : ℝ) : ℂ) * (b - a)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = (1 - w) * ‖a - u‖ + w * ‖b - v‖ + |c - w| * ‖b - a‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : 0 ≤ 1 - w), abs_of_nonneg hw.1]
    _ ≤ ‖a - u‖ + ‖b - v‖ + |c - w| * 2 :=
      add_le_add (add_le_add (mul_le_of_le_one_left (norm_nonneg _) (by linarith))
        (mul_le_of_le_one_left (norm_nonneg _) hw.2))
        (mul_le_mul_of_nonneg_left hba (abs_nonneg _))
    _ = _ := by ring

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

theorem quadraticSquareTriple_norm (b : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.quadraticSquareTriple b x‖ ≤ 1 := by
  simp only [quadraticSquareTriple, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans
      (W.norm_eval _ _))).trans (W.norm_eval _ _)

noncomputable def wrappedDiagonalCorrection (N : ℕ)
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  ∑ k, W.diagonalWrapCoefficient N a.2 k x * F (a.1, k) b x

noncomputable def cyclicDiagonalCorrection (N : ℕ) (δ : ℝ≥0)
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  (1 - (smoothCyclicCarry N δ x : ℂ)) * F a b x +
    (smoothCyclicCarry N δ x : ℂ) * W.wrappedDiagonalCorrection N F a b x

theorem wrappedDiagonalCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.quadraticDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))) -
        F a b (fun z => ((x z).val : ℤ))‖) ≤ ε)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.wrappedDiagonalDerivative N a (fun z => ((x z).val : ℤ)) *
          star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))) -
        W.wrappedDiagonalCorrection N F a b (fun z => ((x z).val : ℤ))‖) ≤ W.outputDim * ε := by
  have hpoint (x : Fin 2 → ℤ) :
      ‖W.wrappedDiagonalDerivative N a x * star (W.quadraticSquareTriple b x) -
        W.wrappedDiagonalCorrection N F a b x‖ ≤
      ∑ k, ‖W.quadraticDiagonalDerivative (a.1, k) x * star (W.quadraticSquareTriple b x) -
        F (a.1, k) b x‖ := by
    have heq : W.wrappedDiagonalDerivative N a x * star (W.quadraticSquareTriple b x) -
        W.wrappedDiagonalCorrection N F a b x =
        ∑ k, W.diagonalWrapCoefficient N a.2 k x *
          (W.quadraticDiagonalDerivative (a.1, k) x * star (W.quadraticSquareTriple b x) -
            F (a.1, k) b x) := by
      rw [W.wrappedDiagonalDerivative_resolution, Finset.sum_mul]
      simp only [wrappedDiagonalCorrection, mul_sub, Finset.sum_sub_distrib, mul_assoc]
    rw [heq]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro k _
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (W.diagonalWrapCoefficient_norm N a.2 k x)
  calc
    _ ≤ 𝔼 x : Fin 2 → ZMod N,
        ∑ k, ‖W.quadraticDiagonalDerivative (a.1, k) (fun z => ((x z).val : ℤ)) *
            star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))) -
          F (a.1, k) b (fun z => ((x z).val : ℤ))‖ :=
      Finset.expect_le_expect (fun x _ => hpoint _)
    _ = ∑ k, 𝔼 x : Fin 2 → ZMod N,
        ‖W.quadraticDiagonalDerivative (a.1, k) (fun z => ((x z).val : ℤ)) *
            star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))) -
          F (a.1, k) b (fun z => ((x z).val : ℤ))‖ := Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _k : Fin W.outputDim, ε := Finset.sum_le_sum (fun k _ => herr (a.1, k) b)
    _ = _ := by simp

theorem cyclicDiagonalCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (δ : ℝ≥0) (hδ : 0 < δ)
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.quadraticDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))) -
        F a b (fun z => ((x z).val : ℤ))‖) ≤ ε)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.cyclicDiagonalDerivative a x * star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))) -
        W.cyclicDiagonalCorrection N δ F a b (fun z => ((x z).val : ℤ))‖) ≤
      (W.outputDim + 1) * ε + 12 * (δ : ℝ) + 2 / N := by
  have hpoint (x : Fin 2 → ZMod N) := norm_smoothed_branch_error
    (cyclicCarry (x 0) (x 1)) (smoothCyclicCarry N δ (fun z => ((x z).val : ℤ)))
    (circleCarryCutoff_range δ _)
    (W.quadraticDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
      star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))))
    (W.wrappedDiagonalDerivative N a (fun z => ((x z).val : ℤ)) *
      star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))))
    (F a b (fun z => ((x z).val : ℤ)))
    (W.wrappedDiagonalCorrection N F a b (fun z => ((x z).val : ℤ)))
    (by
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (W.quadraticDiagonalDerivative_norm a _)).trans (W.quadraticSquareTriple_norm b _))
    (by
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (W.wrappedDiagonalDerivative_norm N a _)).trans (W.quadraticSquareTriple_norm b _))
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun x _ => hpoint x)
  simp only [Complex.ofReal_sub, Complex.ofReal_one, ← mul_assoc, ← add_mul,
    ← W.cyclicDiagonalDerivative_branches] at hm
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect] at hm
  have hi := herr a b
  have hw := W.wrappedDiagonalCorrection_mean_error F herr a b
  have hc := smoothCyclicCarry_mean_error (N := N) δ hδ
  dsimp only [cyclicDiagonalCorrection]
  exact hm.trans ((add_le_add (add_le_add hi hw)
    (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2))).trans_eq (by ring))

theorem exists_cyclicDiagonalCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q e : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (N : ℕ)
      (δ : ℝ≥0), 0 < δ → 0 ≤ q → 0 ≤ e → (δ : ℝ)⁻¹ ≤ Real.exp e →
      ∀ F : (Fin W.outputDim × Fin W.outputDim) →
          (Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) → (Fin 2 → ℤ) → ℂ,
        (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q (F a b))) →
        ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
          ((p + q + e + C) ^ C) (W.cyclicDiagonalCorrection N δ F a b)) := by
  obtain ⟨A, _, hwrap⟩ := exists_diagonalWrapCoefficient_expansion
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + Polynomial.C A) ^ A + X + 6
  let T := (R + Polynomial.C B) ^ B + X + R + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B + T + 2)
  refine ⟨C, hC, ?_⟩
  intro p q e W N δ hδ hq he hinv F hF a b
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q + e
  let r := (v + A) ^ A + v + 6
  let t := (r + B) ^ B + v + r + 2
  let d := (t + B) ^ B + t
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have har : (p + A) ^ A ≤ r := by
    calc
      _ ≤ (v + A) ^ A := pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) A
      _ ≤ r := by dsimp [r]; linarith
  have hqr : q ≤ r := by
    have : 0 ≤ (v + A) ^ A := by positivity
    dsimp [r, v]
    linarith
  have her : e + 4 ≤ r := by
    have : 0 ≤ (v + A) ^ A := by positivity
    dsimp [r, v]
    linarith
  have hrt : r ≤ t := by
    have : 0 ≤ (r + B) ^ B := by positivity
    dsimp [t]
    linarith
  have hwt : (r + B) ^ B + p ≤ t := by dsimp [t, v]; linarith
  have htd : t ≤ d := le_add_of_nonneg_left (by positivity)
  have hpd : (t + B) ^ B ≤ d := le_add_of_nonneg_right ht
  have hcost : d + 2 ≤ (p + q + e + C) ^ C := by
    simpa [X, R, T, r, t, d, v, Polynomial.eval₂_pow] using hbudget v hv
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have hcoeff : (∑ _k : Fin W.outputDim, ‖(1 : ℂ)‖) ≤ Real.exp p := by simpa using hdim
  have hterms (k : Fin W.outputDim) := hmul hr
    ((Classical.choice (hwrap W N a.2 k)).mono har) ((Classical.choice (hF (a.1, k) b)).mono hqr)
  have EW : NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 t
      (W.wrappedDiagonalCorrection N F a b) := by
    have E := (NativeIntegerExpansion.weightedSum (fun k => Classical.choice (hterms k))
      (fun _ => (1 : ℂ)) hp hdim hcoeff).mono hwt
    change NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 t
      (fun x => ∑ k, W.diagonalWrapCoefficient N a.2 k x * F (a.1, k) b x)
    simpa only [one_mul] using E
  let w := fun x => (smoothCyclicCarry N δ x : ℂ)
  have EC := (Classical.choice (exists_smoothCyclicCarry_expansion N δ hδ he hinv)).mono (her.trans hrt)
  have E₀ := (Classical.choice (hF a b)).mono (hqr.trans (hrt.trans htd))
  have E₁ := (Classical.choice (hmul ht EC EW)).mono hpd
  have E₂ := (Classical.choice (hmul ht EC ((Classical.choice (hF a b)).mono (hqr.trans hrt)))).mono hpd
  let fs : Fin 3 → (Fin 2 → ℤ) → ℂ := ![F a b,
    (fun x => w x * W.wrappedDiagonalCorrection N F a b x), (fun x => w x * F a b x)]
  have Efs (j : Fin 3) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 d (fs j)) := by
    fin_cases j
    · exact ⟨E₀⟩
    · exact ⟨E₁⟩
    · exact ⟨E₂⟩
  let cs : Fin 3 → ℂ := ![1, 1, -1]
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have E := (NativeIntegerExpansion.weightedSum (fun j => Classical.choice (Efs j)) cs
    (by norm_num : (0 : ℝ) ≤ 2) (by simpa using hthree)
    (by convert hthree using 1; norm_num [cs, Fin.sum_univ_succ])).mono hcost
  have heq : (fun x => ∑ j, cs j * fs j x) = W.cyclicDiagonalCorrection N δ F a b := by
    funext x
    simp [cs, fs, Fin.sum_univ_succ, w, cyclicDiagonalCorrection]
    ring
  exact ⟨heq ▸ E⟩

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def integerSecondDifference (u v : (Fin 2 → ℤ) → ℂ) (k : ℤ)
    (x : Fin 2 → ℤ) : ℂ := u x * star (v ![x 0, x 1 + k])

noncomputable def cyclicSecondDifference {N : ℕ} (u v : (Fin 2 → ℤ) → ℂ)
    (k : ZMod N) (h : ℤ) (n : ZMod N) : ℂ :=
  u ![h, (n.val : ℤ)] * star (v ![h, ((n + k).val : ℤ)])

noncomputable def smoothedSecondDifference (N : ℕ) (δ : ℝ≥0)
    (u v : (Fin 2 → ℤ) → ℂ) (k : ℤ) (x : Fin 2 → ℤ) : ℂ :=
  (1 - (smoothCyclicCarry N δ ![k, x 1] : ℂ)) * integerSecondDifference u v k x +
    (smoothCyclicCarry N δ ![k, x 1] : ℂ) * integerSecondDifference u v (k - N) x

theorem integerSecondDifference_norm (u v : (Fin 2 → ℤ) → ℂ)
    (hu : ∀ x, ‖u x‖ ≤ 1) (hv : ∀ x, ‖v x‖ ≤ 1) (k : ℤ) (x : Fin 2 → ℤ) :
    ‖integerSecondDifference u v k x‖ ≤ 1 := by
  rw [integerSecondDifference, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hu _)).trans (hv _)

theorem cyclicSecondDifference_branches {N : ℕ} [NeZero N]
    (u v : (Fin 2 → ℤ) → ℂ) (k : ZMod N) (h : ℤ) (n : ZMod N) :
    cyclicSecondDifference u v k h n =
      (1 - (cyclicCarry k n : ℂ)) * integerSecondDifference u v k.val ![h, (n.val : ℤ)] +
        (cyclicCarry k n : ℂ) * integerSecondDifference u v ((k.val : ℤ) - N) ![h, (n.val : ℤ)] := by
  have hval : ((n + k).val : ℤ) = (n.val : ℤ) + k.val -
      if N - k.val ≤ n.val then (N : ℤ) else 0 := by
    simpa only [add_comm n k] using cyclic_representative_add k n
  have hk := k.val_lt
  by_cases hw : N ≤ k.val + n.val
  · have hcut : N - k.val ≤ n.val := by omega
    simp only [cyclicCarry, hw, ite_true, Complex.ofReal_one, sub_self, zero_mul, one_mul, zero_add,
      cyclicSecondDifference, integerSecondDifference, Matrix.cons_val_zero, Matrix.cons_val_one,
      hval, ite_eq_left hcut]
    rw [add_sub_assoc]
  · have hcut : ¬N - k.val ≤ n.val := by omega
    simp only [cyclicCarry, hw, ite_false, Complex.ofReal_zero, sub_zero, zero_mul, one_mul, add_zero,
      cyclicSecondDifference, integerSecondDifference, Matrix.cons_val_zero, Matrix.cons_val_one,
      hval, ite_eq_right hcut]

theorem smoothedSecondDifference_mean_error {N : ℕ} [NeZero N]
    (δ : ℝ≥0) (hδ : 0 < δ) (u v : (Fin 2 → ℤ) → ℂ)
    (hu : ∀ x, ‖u x‖ ≤ 1) (hv : ∀ x, ‖v x‖ ≤ 1) (k : ZMod N) (h : ℤ) :
    (𝔼 n : ZMod N, ‖cyclicSecondDifference u v k h n -
      smoothedSecondDifference N δ u v k.val ![h, (n.val : ℤ)]‖) ≤
        12 * (δ : ℝ) + 2 / N := by
  have hp (n : ZMod N) : ‖cyclicSecondDifference u v k h n -
      smoothedSecondDifference N δ u v k.val ![h, (n.val : ℤ)]‖ ≤
        2 * |cyclicCarry k n - smoothCyclicCarry N δ ![(k.val : ℤ), (n.val : ℤ)]| := by
    have hh := norm_smoothed_branch_error (cyclicCarry k n)
      (smoothCyclicCarry N δ ![(k.val : ℤ), (n.val : ℤ)]) (circleCarryCutoff_range δ _)
      (integerSecondDifference u v k.val ![h, (n.val : ℤ)])
      (integerSecondDifference u v ((k.val : ℤ) - N) ![h, (n.val : ℤ)])
      (integerSecondDifference u v k.val ![h, (n.val : ℤ)])
      (integerSecondDifference u v ((k.val : ℤ) - N) ![h, (n.val : ℤ)])
      (integerSecondDifference_norm u v hu hv _ _)
      (integerSecondDifference_norm u v hu hv _ _)
    simpa only [Complex.ofReal_sub, Complex.ofReal_one, sub_self, norm_zero, zero_add,
      ← cyclicSecondDifference_branches, smoothedSecondDifference, Matrix.cons_val_one,
      Matrix.cons_val_zero] using hh
  calc
    _ ≤ 𝔼 n : ZMod N,
        2 * |cyclicCarry k n - smoothCyclicCarry N δ ![(k.val : ℤ), (n.val : ℤ)]| :=
      Finset.expect_le_expect (fun n _ => hp n)
    _ = 2 * (𝔼 n : ZMod N,
        |cyclicCarry k n - smoothCyclicCarry N δ ![(k.val : ℤ), (n.val : ℤ)]|) :=
      (Finset.mul_expect _ _ _).symm
    _ ≤ 2 * (6 * (δ : ℝ) + 1 / N) :=
      mul_le_mul_of_nonneg_left (smoothCyclicCarry_fixed_shift_mean_error δ hδ k) (by norm_num)
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators NNReal

theorem exists_diagonalSquareCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p), 0 ≤ q →
      ∀ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q (G a b))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
        ((p + q + C) ^ C) (W.diagonalSquareCorrection G a b)) := by
  obtain ⟨A, _, hdiag⟩ := exists_quadratic_diagonal_derivative_equivalence
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + Polynomial.C A) ^ A + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C B) ^ B + X)
  refine ⟨C, hC, ?_⟩
  intro p q W hq G hG a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q
  let r := (v + A) ^ A + v + 2
  have hv : 0 ≤ v := add_nonneg hp hq
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hqr : q ≤ r := by
    have : 0 ≤ (v + A) ^ A := by positivity
    dsimp [r, v]
    linarith
  have hAr : (p + A) ^ A ≤ r := by
    calc
      _ ≤ (v + A) ^ A := pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) A
      _ ≤ r := by dsimp [r]; linarith
  have hcost : (r + B) ^ B + p ≤ (p + q + C) ^ C := by
    have hh : (r + B) ^ B + v ≤ (p + q + C) ^ C := by
      simpa [X, R, r, v, Polynomial.eval₂_pow] using hbudget v hv
    dsimp [v] at hh
    linarith
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have hcoeff : (∑ _j : Fin W.outputDim, ‖(1 : ℂ)‖) ≤ Real.exp p := by simpa using hdim
  have hterm (j : Fin W.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((r + B) ^ B)
        (fun x => (W.quadraticDiagonalDerivative a x * star (W.quadraticMixedTriple (j, b.2) x)) *
          star (G b.1 j x))) :=
    hmul hr ((Classical.choice ((hdiag W).expansion a (j, b.2))).mono hAr)
      ((Classical.choice (hG b.1 j)).conjugate.mono hqr)
  have E := (NativeIntegerExpansion.weightedSum (fun j => Classical.choice (hterm j))
    (fun _ => (1 : ℂ)) hp hdim hcoeff).mono hcost
  change Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + C) ^ C)
    (fun x => ∑ j, (W.quadraticDiagonalDerivative a x * star (W.quadraticMixedTriple (j, b.2) x)) *
      star (G b.1 j x)))
  exact ⟨by simpa only [one_mul] using E⟩

theorem exists_cyclicExchangeCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q e : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (N : ℕ)
      (δ : ℝ≥0), 0 < δ → 0 ≤ q → 0 ≤ e → (δ : ℝ)⁻¹ ≤ Real.exp e →
      ∀ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q (G a b))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + e + C) ^ C)
        (W.cyclicDiagonalCorrection N δ (W.diagonalSquareCorrection G) a b)) := by
  obtain ⟨A, _, hdiag⟩ := exists_diagonalSquareCorrection_expansion
  obtain ⟨B, _, hcyclic⟩ := exists_cyclicDiagonalCorrection_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + (X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q e W N δ hδ hq he hinv G hG a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hA : (p + q + A) ^ A ≤ (p + q + e + A) ^ A :=
    pow_le_pow_left₀ (by positivity) (by linarith) A
  have hb : (p + (p + q + A) ^ A + e + B) ^ B ≤ (p + q + e + C) ^ C := by
    have hh : (p + q + e + (p + q + e + A) ^ A + B) ^ B ≤ (p + q + e + C) ^ C := by
      simpa [X, Polynomial.eval₂_pow] using hbudget (p + q + e) (by positivity)
    apply le_trans _ hh
    apply pow_le_pow_left₀ (by positivity)
    linarith
  obtain ⟨E⟩ := hcyclic W N δ hδ (by positivity : 0 ≤ (p + q + A) ^ A) he hinv
    (W.diagonalSquareCorrection G) (hdiag W hq G hG) a b
  exact ⟨E.mono hb⟩

theorem cyclicExchangeCorrection_mean_error {p ε : ℝ} {N : ℕ} [NeZero N]
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (δ : ℝ≥0) (hδ : 0 < δ)
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.antisymmetricKernel a b ((x 0).val : ℤ) ((x 1).val : ℤ) -
        G a b (fun k => ((x k).val : ℤ))‖) ≤ ε) (a b) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.cyclicDiagonalDerivative a x * star (W.quadraticSquareTriple b (fun k => ((x k).val : ℤ))) -
        W.cyclicDiagonalCorrection N δ (W.diagonalSquareCorrection G) a b
          (fun k => ((x k).val : ℤ))‖) ≤
      (W.outputDim + 1) * (W.outputDim * ε) + 12 * (δ : ℝ) + 2 / N :=
  W.cyclicDiagonalCorrection_mean_error δ hδ (W.diagonalSquareCorrection G)
    (W.diagonalSquareCorrection_mean_error G herr) a b

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem exists_smoothedSecondDifference_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      ∀ (N : ℕ) (δ : ℝ≥0), 0 < δ → (δ : ℝ)⁻¹ ≤ Real.exp e →
      ∀ (u v : (Fin 2 → ℤ) → ℂ) (k : ℤ),
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 p (integerSecondDifference u v k)) →
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 p (integerSecondDifference u v (k - N))) →
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + e + C) ^ C)
        (smoothedSecondDifference N δ u v k)) := by
  obtain ⟨A, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let R := X + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((R + Polynomial.C A) ^ A + R + 2)
  refine ⟨C, hC, ?_⟩
  intro p e hp he N δ hδ hinv u v k ⟨E0⟩ ⟨E1⟩
  let r := p + e + 4
  let t := (r + A) ^ A + r
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hpr : p ≤ r := by dsimp [r]; linarith
  have her : e + 4 ≤ r := by dsimp [r]; linarith
  have hrt : r ≤ t := le_add_of_nonneg_left (by positivity)
  have hmt : (r + A) ^ A ≤ t := le_add_of_nonneg_right hr
  have htC : t + 2 ≤ (p + e + C) ^ C := by
    simpa [X, R, r, t, Polynomial.eval₂_pow] using hbudget (p + e) (by linarith)
  obtain ⟨EC⟩ := exists_fixed_shift_smoothCyclicCarry_expansion N δ hδ he hinv k
  obtain ⟨EM0⟩ := hmul hr (EC.mono her) (E0.mono hpr)
  obtain ⟨EM1⟩ := hmul hr (EC.mono her) (E1.mono hpr)
  let w (x : Fin 2 → ℤ) := (smoothCyclicCarry N δ ![k, x 1] : ℂ)
  let fs : Fin 3 → (Fin 2 → ℤ) → ℂ := ![integerSecondDifference u v k,
    (fun x => w x * integerSecondDifference u v (k - N) x),
    (fun x => w x * integerSecondDifference u v k x)]
  have Efs (j : Fin 3) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 t (fs j)) := by
    fin_cases j
    · exact ⟨E0.mono (hpr.trans hrt)⟩
    · exact ⟨EM1.mono hmt⟩
    · exact ⟨EM0.mono hmt⟩
  let cs : Fin 3 → ℂ := ![1, 1, -1]
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have E := (NativeIntegerExpansion.weightedSum (fun j => Classical.choice (Efs j)) cs
    (by norm_num : (0 : ℝ) ≤ 2) (by simpa using hthree)
    (by convert hthree using 1; norm_num [cs, Fin.sum_univ_succ])).mono htC
  have heq : (fun x => ∑ j, cs j * fs j x) = smoothedSecondDifference N δ u v k := by
    funext x
    simp [cs, fs, w, Fin.sum_univ_succ, smoothedSecondDifference]
    ring
  exact ⟨heq ▸ E⟩

theorem exists_cyclicSecondDifference_approximation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      ∀ {N : ℕ} [NeZero N], Real.exp (e + 16) ≤ (N : ℝ) →
      ∀ (u v : (Fin 2 → ℤ) → ℂ), (∀ x, ‖u x‖ ≤ 1) → (∀ x, ‖v x‖ ≤ 1) →
      (∀ k : ℤ, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 p
        (integerSecondDifference u v k))) →
      ∀ k : ZMod N, ∃ K : (Fin 2 → ℤ) → ℂ,
        Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + e + C) ^ C) K) ∧
        ∀ h : ℤ, (𝔼 n : ZMod N,
          ‖cyclicSecondDifference u v k h n - K ![h, (n.val : ℤ)]‖) ≤ Real.exp (-e) := by
  obtain ⟨A, _, hexpand⟩ := exists_smoothedSecondDifference_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + 16 + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro p e hp he N _ hN u v hu hv hmodel k
  let δ : ℝ≥0 := ⟨Real.exp (-(e + 16)), (Real.exp_pos _).le⟩
  have hδ : 0 < δ := Real.exp_pos _
  have hinv : (δ : ℝ)⁻¹ ≤ Real.exp (e + 16) := by
    change (Real.exp (-(e + 16)))⁻¹ ≤ Real.exp (e + 16)
    rw [← Real.exp_neg, neg_neg]
  have hbudget' : (p + (e + 16) + A) ^ A ≤ (p + e + C) ^ C := by
    have hb := hbudget (p + e) (by linarith)
    simpa [X, Polynomial.eval₂_pow, add_assoc] using hb
  obtain ⟨E⟩ := hexpand hp (by linarith : 0 ≤ e + 16) N δ hδ hinv u v k.val
    (hmodel k.val) (hmodel ((k.val : ℤ) - N))
  refine ⟨smoothedSecondDifference N δ u v k.val, ⟨E.mono hbudget'⟩, ?_⟩
  intro h
  apply (smoothedSecondDifference_mean_error δ hδ u v hu hv k h).trans
  have hNinv : 1 / (N : ℝ) ≤ Real.exp (-(e + 16)) := by
    have hh := one_div_le_one_div_of_le (Real.exp_pos (e + 16)) hN
    simpa only [one_div, ← Real.exp_neg] using hh
  have htwo : 2 / (N : ℝ) ≤ 2 * Real.exp (-(e + 16)) := by
    calc
      _ = 2 * (1 / (N : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hNinv (by norm_num)
  calc
    12 * (δ : ℝ) + 2 / N ≤ 14 * Real.exp (-(e + 16)) := by
      change 12 * Real.exp (-(e + 16)) + 2 / (N : ℝ) ≤ 14 * Real.exp (-(e + 16))
      linarith only [htwo]
    _ ≤ Real.exp 16 * Real.exp (-(e + 16)) := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (16 : ℝ)]) (Real.exp_nonneg _)
    _ = Real.exp (-e) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators NNReal

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def quadraticRoot :
    NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) (tensorPowerBudget 2 p) :=
  (W.rationalDilation (1 / 2)).tensorPower 2

noncomputable def rootExchangeCorrection
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) :=
  (W.rationalDilation (1 / 2)).tensorSquareExchangeCorrection (W.halfDilationExchangeCorrection G)

noncomputable def rootCyclicCorrection (N : ℕ) (δ : ℝ≥0)
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) :=
  W.quadraticRoot.cyclicDiagonalCorrection N δ
    (W.quadraticRoot.diagonalSquareCorrection (W.rootExchangeCorrection G))

theorem rootCyclicCorrection_mean_error {N : ℕ} [NeZero N] (δ : ℝ≥0) (hδ : 0 < δ)
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) {ε : ℝ}
    (hcap : ∀ i j (x : Fin 2 → ZMod N), ‖G i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (herr : ∀ i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.antisymmetricKernel i j ((x 0).val : ℤ) ((x 1).val : ℤ) -
        G i j (fun k => ((x k).val : ℤ))‖) ≤ ε) (a b) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.quadraticRoot.cyclicDiagonalDerivative a x *
          star (W.quadraticRoot.quadraticSquareTriple b (fun k => ((x k).val : ℤ))) -
        W.rootCyclicCorrection N δ G a b (fun k => ((x k).val : ℤ))‖) ≤
      (W.quadraticRoot.outputDim + 1) *
        (W.quadraticRoot.outputDim * ((1 + (W.outputDim : ℝ) ^ 2) * (4 * (W.outputDim : ℝ) ^ 2 * ε))) +
        12 * (δ : ℝ) + 2 / N := by
  exact W.quadraticRoot.cyclicExchangeCorrection_mean_error δ hδ (W.rootExchangeCorrection G)
    (W.explicit_half_root_exchange_mean_error G hcap herr) a b

theorem exists_rootCyclicCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q e : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (N : ℕ) (δ : ℝ≥0),
      0 < δ → 0 ≤ q → 0 ≤ e → (δ : ℝ)⁻¹ ≤ Real.exp e →
      ∀ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q (G a b))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + e + C) ^ C)
        (W.rootCyclicCorrection N δ G a b)) := by
  obtain ⟨A, _, hroot⟩ := exists_explicit_half_root_exchange_expansion
  obtain ⟨B, _, hcyclic⟩ := exists_cyclicExchangeCorrection_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((3 * (X + 1) + (X + Polynomial.C A) ^ A + X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q e W N δ hδ hq he hinv G hG a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q + e
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hA : (p + q + A) ^ A ≤ (v + A) ^ A :=
    pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) A
  have hbound : (tensorPowerBudget 2 p + (p + q + A) ^ A + e + B) ^ B ≤
      (p + q + e + C) ^ C := by
    have hh : (3 * (v + 1) + (v + A) ^ A + v + B) ^ B ≤ (v + C) ^ C := by
      simpa [X, Polynomial.eval₂_pow] using hbudget v hv
    apply le_trans _ hh
    apply pow_le_pow_left₀ (by unfold tensorPowerBudget; positivity)
    norm_num only [tensorPowerBudget, Nat.cast_ofNat] at *
    dsimp [v] at *
    linarith
  obtain ⟨E⟩ := hcyclic W.quadraticRoot N δ hδ (by positivity : 0 ≤ (p + q + A) ^ A) he hinv
    (W.rootExchangeCorrection G) (hroot W hq G hG) a b
  exact ⟨E.mono hbound⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct BigOperators

theorem exists_cyclic_second_difference_models :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} {I : Type*} [Fintype I]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L 2 d) {p e : ℝ}
      (V : D.UnitVerticalObservable (D.filtration.realification.subgroup 2) I p)
      (g : D.filtration.realification.PolynomialOrbit (fun _ : Fin 2 => 1)),
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card I : ℝ) ≤ Real.exp p → 0 ≤ e →
      ∀ {N : ℕ} [NeZero N], Real.exp (e + 16) ≤ (N : ℝ) →
      ∀ (i j : I) (k : ZMod N), ∃ K : (Fin 2 → ℤ) → ℂ,
        Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + e + C) ^ C) K) ∧
        ∀ h : ℤ, (𝔼 n : ZMod N,
          ‖cyclicSecondDifference (V.test g i).eval (V.test g j).eval k h n -
            K ![h, (n.val : ℤ)]‖) ≤ Real.exp (-e) := by
  obtain ⟨A, _, htranslate⟩ := exists_integer_translation_equivalence_budget 1
  obtain ⟨B, _, happrox⟩ := exists_cyclicSecondDifference_approximation
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro L I _ _ _ _ _ _ _ d D p e V g hp hD hI he N _ hN i j k
  let r := (p + A) ^ A
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hmodels (t : ℤ) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 r
      (integerSecondDifference (V.test g i).eval (V.test g j).eval t)) := by
    have E := (htranslate D V g hp hD hI 0 ![0, t]).expansion i j
    change Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 r
      (fun x => (V.test g i).eval (x + 0) * star ((V.test g j).eval (x + ![0, t])))) at E
    have hshift (x : Fin 2 → ℤ) : x + ![0, t] = ![x 0, x 1 + t] := by
      funext a
      fin_cases a <;> simp
    change Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 r
      (fun x => (V.test g i).eval x * star ((V.test g j).eval ![x 0, x 1 + t])))
    simpa only [add_zero, hshift] using E
  have hcost : (r + e + B) ^ B ≤ (p + e + C) ^ C := by
    have hbase : r ≤ (p + e + A) ^ A := by
      apply pow_le_pow_left₀ (by positivity)
      linarith
    have hb : ((p + e + A) ^ A + (p + e) + B) ^ B ≤ (p + e + C) ^ C := by
      simpa [X, Polynomial.eval₂_pow] using hbudget (p + e) (by linarith)
    exact (pow_le_pow_left₀ (by positivity) (by linarith) B).trans hb
  obtain ⟨K, ⟨E⟩, herr⟩ := happrox hr he hN (V.test g i).eval (V.test g j).eval
    (fun x => (V.test g i).norm_eval_le x) (fun x => (V.test g j).norm_eval_le x) hmodels k
  exact ⟨K, ⟨E.mono hcost⟩, herr⟩

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

end OAI
