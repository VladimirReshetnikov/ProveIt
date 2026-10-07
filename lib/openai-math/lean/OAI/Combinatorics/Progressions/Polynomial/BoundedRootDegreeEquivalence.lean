import OAI.Combinatorics.Progressions.Estimates.NativeMultidegreeDilation
import OAI.Combinatorics.Progressions.Estimates.TensorSquarePairComparison

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_dilation_degree_equivalence {σ : Type*} [Fintype σ] [DecidableEq σ]
    (bound : σ → ℕ) (hpos : 1 ≤ ∑ j, bound j) (q : ℤ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p),
      NativeIntegerVectorEquivalence ((∑ j, bound j) - 1) ((p + C) ^ C)
        (integerDilationVector W.eval q) (signedTensorVector W.eval (q ^ ∑ j, bound j)) := by
  obtain ⟨a, _, hfamily⟩ := exists_dilation_family bound hpos q
  let n := (q ^ ∑ j, bound j).natAbs
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a) ^ a + Polynomial.C (n + 1) * X + 2)
  refine ⟨C, hC, ?_⟩
  intro p W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hb : (p + a) ^ a + (n + 1 : ℝ) * p + 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow, Nat.cast_add] using hbudget p hp
  have hpr : p ≤ (p + C) ^ C := by nlinarith [mul_nonneg hn hp]
  have hnpr : (n : ℝ) * p ≤ (p + C) ^ C := by nlinarith
  have har : (p + a) ^ a ≤ (p + C) ^ C := by nlinarith [mul_nonneg hn hp]
  obtain ⟨R, _⟩ := hfamily W
  exact NativeIntegerVectorEquivalence.of_dilation_family W.eval q (∑ j, bound j) R
    (by simpa only [Fintype.card_fin] using W.output_bound) hpr hnpr har

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_root_degree_equivalence {σ : Type*} [Fintype σ] [DecidableEq σ]
    (bound : σ → ℕ) (hpos : 1 ≤ ∑ j, bound j) (q : ℕ) (hq : 0 < q) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p),
      ∃ R : NativeMultidegreeNilcharacter bound ((p + C) ^ C),
        R.dim = W.dim ∧
        NativeIntegerVectorEquivalence ((∑ j, bound j) - 1) ((p + C) ^ C)
          W.eval (tensorVector R.eval q) := by
  obtain ⟨a, _, hdilation⟩ := exists_dilation_degree_equivalence bound hpos (q : ℤ)
  let n := q ^ ((∑ j, bound j) - 1)
  let X : Polynomial ℕ := Polynomial.X
  let B := Polynomial.C (n + 1) * (X + 1)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a) ^ a + Polynomial.C (q + 1) * B + X + 2)
  refine ⟨C, hC, ?_⟩
  intro p W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hA : 0 ≤ (p + a) ^ a := by positivity
  have hB : 0 ≤ tensorPowerBudget n p := by unfold tensorPowerBudget; positivity
  have hqB : 0 ≤ (q : ℝ) * tensorPowerBudget n p := mul_nonneg (Nat.cast_nonneg _) hB
  have hb : (p + a) ^ a + (q + 1 : ℝ) * tensorPowerBudget n p + p + 2 ≤ (p + C) ^ C := by
    simpa [X, B, tensorPowerBudget, Polynomial.eval₂_pow, Nat.cast_add] using hbudget p hp
  have hpr : p ≤ (p + C) ^ C := by nlinarith
  have hBr : tensorPowerBudget n p ≤ (p + C) ^ C := by nlinarith
  have hqBr : (q : ℝ) * tensorPowerBudget n p ≤ (p + C) ^ C := by nlinarith
  have hAr : (p + a) ^ a ≤ (p + C) ^ C := by nlinarith
  let V := W.rationalDilation ((q : ℚ)⁻¹)
  let R₀ := V.tensorPower n
  let R := R₀.mono hBr
  have hscale : (q : ℚ)⁻¹ * ((q : ℤ) : ℚ) = 1 := by
    rw [Int.cast_natCast]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hq.ne')
  have hleft (i : Fin W.outputDim) (x : σ → ℤ) :
      W.eval i x = integerDilationVector V.eval (q : ℤ) i x :=
    (W.rationalDilation_eval_rescaled _ _ hscale i x).symm
  have hright (b : Fin q → Fin R.outputDim) (x : σ → ℤ) :
      tensorVector R.eval q b x =
        signedTensorVector V.eval ((q : ℤ) ^ ∑ j, bound j)
          (rootTensorIndex W.outputDim q (∑ j, bound j) hpos b) x := by
    change tensorVector (V.tensorPower n).eval q b x = _
    exact V.tensorPower_tensor_eval q (∑ j, bound j) hpos b x
  have hdim : (Fintype.card (Fin q → Fin R.outputDim) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    have hroot : (R.outputDim : ℝ) ≤ Real.exp (tensorPowerBudget n p) := R₀.output_bound
    calc
      _ ≤ Real.exp (tensorPowerBudget n p) ^ q := pow_le_pow_left₀ (Nat.cast_nonneg _) hroot _
      _ = Real.exp ((q : ℝ) * tensorPowerBudget n p) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr hqBr
  refine ⟨R, rfl, ?_⟩
  exact (hdilation V).of_coordinate_maps W.eval (tensorVector R.eval q) id
    (rootTensorIndex W.outputDim q (∑ j, bound j) hpos) hleft hright
    (by simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpr)) hdim hAr

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold.MultidegreeStructure
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_uniform_dilation_degree_equivalence (s : ℕ) (q : ℤ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} [Fintype σ] [DecidableEq σ]
      (bound : σ → ℕ), (∑ j, bound j) = s + 1 →
      ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p),
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (integerDilationVector W.eval q) (signedTensorVector W.eval (q ^ (s + 1))) := by
  obtain ⟨a, _, hfamily⟩ := exists_controlled_dilation_family s q
  let n := (q ^ (s + 1)).natAbs
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a) ^ a + Polynomial.C (n + 1) * X + 2)
  refine ⟨C, hC, ?_⟩
  intro σ _ _ bound hs p W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hb : (p + a) ^ a + (n + 1 : ℝ) * p + 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow, Nat.cast_add] using hbudget p hp
  have hpr : p ≤ (p + C) ^ C := by nlinarith [mul_nonneg hn hp]
  have hnpr : (n : ℝ) * p ≤ (p + C) ^ C := by nlinarith
  have har : (p + a) ^ a ≤ (p + C) ^ C := by nlinarith [mul_nonneg hn hp]
  obtain ⟨R, _⟩ := hfamily W.model W.multi rfl hs W.complexity W.vertical W.orbit
  have R' : NativeIntegerModelFamily (fun _ : σ => 1) s ((p + a) ^ a)
      (dilationTensorCrossProduct W.eval q (s + 1)) := by
    exact hs ▸ R
  exact NativeIntegerVectorEquivalence.of_dilation_family W.eval q (s + 1) R'
    (by simpa only [Fintype.card_fin] using W.output_bound) hpr hnpr har

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_uniform_root_degree_equivalence (s q : ℕ) (hq : 0 < q) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} [Fintype σ] [DecidableEq σ]
      (bound : σ → ℕ), (∑ j, bound j) = s + 1 →
      ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p),
      ∃ R : NativeMultidegreeNilcharacter bound ((p + C) ^ C),
        R.dim = W.dim ∧ NativeIntegerVectorEquivalence s ((p + C) ^ C)
          W.eval (tensorVector R.eval q) := by
  obtain ⟨a, _, hdilation⟩ := exists_uniform_dilation_degree_equivalence s (q : ℤ)
  let n := q ^ s
  let X : Polynomial ℕ := Polynomial.X
  let B := Polynomial.C (n + 1) * (X + 1)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a) ^ a + Polynomial.C (q + 1) * B + X + 2)
  refine ⟨C, hC, ?_⟩
  intro σ _ _ bound hs p W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hA : 0 ≤ (p + a) ^ a := by positivity
  have hB : 0 ≤ tensorPowerBudget n p := by unfold tensorPowerBudget; positivity
  have hqB : 0 ≤ (q : ℝ) * tensorPowerBudget n p := mul_nonneg (Nat.cast_nonneg _) hB
  have hb : (p + a) ^ a + (q + 1 : ℝ) * tensorPowerBudget n p + p + 2 ≤ (p + C) ^ C := by
    simpa [X, B, tensorPowerBudget, Polynomial.eval₂_pow, Nat.cast_add] using hbudget p hp
  have hpr : p ≤ (p + C) ^ C := by nlinarith
  have hBr : tensorPowerBudget n p ≤ (p + C) ^ C := by nlinarith
  have hqBr : (q : ℝ) * tensorPowerBudget n p ≤ (p + C) ^ C := by nlinarith
  have hAr : (p + a) ^ a ≤ (p + C) ^ C := by nlinarith
  let V := W.rationalDilation ((q : ℚ)⁻¹)
  let R₀ := V.tensorPower n
  let R := R₀.mono hBr
  have hscale : (q : ℚ)⁻¹ * ((q : ℤ) : ℚ) = 1 := by
    rw [Int.cast_natCast]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hq.ne')
  have hleft (i : Fin W.outputDim) (x : σ → ℤ) :
      W.eval i x = integerDilationVector V.eval (q : ℤ) i x :=
    (W.rationalDilation_eval_rescaled _ _ hscale i x).symm
  have hpos : 1 ≤ s + 1 := by omega
  have hright (b : Fin q → Fin R.outputDim) (x : σ → ℤ) :
      tensorVector R.eval q b x =
        signedTensorVector V.eval ((q : ℤ) ^ (s + 1))
          (rootTensorIndex W.outputDim q (s + 1) hpos b) x := by
    change tensorVector (V.tensorPower n).eval q b x = _
    exact V.tensorPower_tensor_eval q (s + 1) hpos b x
  have hdim : (Fintype.card (Fin q → Fin R.outputDim) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    have hroot : (R.outputDim : ℝ) ≤ Real.exp (tensorPowerBudget n p) := R₀.output_bound
    calc
      _ ≤ Real.exp (tensorPowerBudget n p) ^ q := pow_le_pow_left₀ (Nat.cast_nonneg _) hroot _
      _ = Real.exp ((q : ℝ) * tensorPowerBudget n p) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr hqBr
  refine ⟨R, rfl, ?_⟩
  exact (hdilation bound hs V).of_coordinate_maps W.eval (tensorVector R.eval q) id
    (rootTensorIndex W.outputDim q (s + 1) hpos) hleft hright
    (by simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpr)) hdim hAr

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_bounded_root_degree_equivalence (s Q : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {q : ℕ}, 0 < q → q ≤ Q →
      ∀ {σ : Type} [Fintype σ] [DecidableEq σ]
        (bound : σ → ℕ), (∑ j, bound j) = s + 1 →
        ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p),
        ∃ R : NativeMultidegreeNilcharacter bound ((p + C) ^ C),
          R.dim = W.dim ∧ NativeIntegerVectorEquivalence s ((p + C) ^ C)
            W.eval (tensorVector R.eval q) := by
  classical
  let a : Fin Q → ℕ := fun i => Classical.choose
    (exists_uniform_root_degree_equivalence.{0} s (i.val + 1) (by omega))
  let C := 2 + ∑ i, a i
  refine ⟨C, by dsimp [C]; omega, ?_⟩
  intro q hq hqQ σ _ _ bound hs p W
  let i : Fin Q := ⟨q - 1, by omega⟩
  have hi : i.val + 1 = q := by dsimp [i]; omega
  have ha : 2 ≤ a i := (Classical.choose_spec
    (exists_uniform_root_degree_equivalence.{0} s (i.val + 1) (by omega))).1
  have hroot : ∀ {τ : Type} [Fintype τ] [DecidableEq τ]
      (b : τ → ℕ), (∑ j, b j) = s + 1 →
      ∀ {r : ℝ} (V : NativeMultidegreeNilcharacter b r),
      ∃ R : NativeMultidegreeNilcharacter b ((r + a i) ^ a i),
        R.dim = V.dim ∧ NativeIntegerVectorEquivalence s ((r + a i) ^ a i)
          V.eval (tensorVector R.eval (i.val + 1)) :=
    (Classical.choose_spec
      (exists_uniform_root_degree_equivalence.{0} s (i.val + 1) (by omega))).2
  rw [hi] at hroot
  obtain ⟨R, hdim, hE⟩ := hroot bound hs W
  have hsum : a i ≤ ∑ j, a j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
  have haC : a i ≤ C := by dsimp [C]; omega
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hbudget := shifted_power_self_mono hp (by omega : 1 ≤ a i) haC
  exact ⟨R.mono hbudget, hdim, hE.mono hbudget⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
