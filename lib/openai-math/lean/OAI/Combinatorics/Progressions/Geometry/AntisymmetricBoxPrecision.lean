import OAI.Combinatorics.Progressions.Estimates.AntisymmetricPartitionApproximation

namespace OAI

section

namespace Erdos3

open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeAntisymmetricFrozenDescent.lie NativeAntisymmetricFrozenDescent.algebra
  NativeAntisymmetricFrozenDescent.topology NativeAntisymmetricFrozenDescent.topologicalAdd
  NativeAntisymmetricFrozenDescent.continuousSMul NativeAntisymmetricFrozenDescent.hausdorff

theorem exists_antisymmetric_box_expansion (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q b t : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {V : NativeAntisymmetricOrbitFactors W N p}
      (R : NativeAntisymmetricFrozenDescent V q) (_L : NativeAntisymmetricLocalModels R b),
      0 ≤ t → q ≤ t → b ≤ t → ∀ {ρ : ℝ}, 0 < ρ → 1 / ρ ≤ Real.exp ((t + 2) ^ a) →
      ∃ F : (Fin 4 → ℤ) → ℂ,
        Nonempty (NativeIntegerExpansion (fun _ : Fin 4 => 1) 1 ((t + C) ^ C) F) ∧
        (𝔼 x : Fin 4 → ZMod N,
          ‖W.antisymmetricBoxValue V.leftIndex V.rightIndex (fun i => ((x i).val : ℤ)) -
            F (fun i => ((x i).val : ℤ))‖) ≤ Real.exp (t + 73) * (ρ + 1 / N) := by
  obtain ⟨A, _, hpartition⟩ := exists_antisymmetric_partition_approximation a
  obtain ⟨B, _, hweighted⟩ := exists_positive_weighted_expansion
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Q + 4 + Polynomial.C B) ^ B + Q)
  refine ⟨C, hC, ?_⟩
  intro p q b t W N _ V R L ht hqt hbt ρ hρ hprec
  classical
  let : NeZero L.period := ⟨L.period_pos.ne'⟩
  obtain ⟨n, _, hcard, ψ, hψ, hsum, S, _hSo, hSc, herr⟩ :=
    hpartition R L ht hqt hbt hρ hprec
  let r := (t + A) ^ A
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr4 : (Fintype.card (Fin 4) : ℝ) ≤ r + 4 := by simpa using hr
  have hcost : (r + 4 + B) ^ B + r ≤ (t + C) ^ C := by
    simpa [Q, X, r, Polynomial.eval₂_pow] using hbudget t ht
  have hfamily (j : Fin 4 → Fin n × ZMod L.period) :
      ∃ g : (Fin 4 → ℤ) → ℂ,
        Nonempty (NativeIntegerExpansion (fun _ : Fin 4 => 1) 1 ((r + 4 + B) ^ B) g) ∧
        ∀ x : Fin 4 → ZMod N, g (fun i => ((x i).val : ℤ)) =
          (∏ i, (ψ (j i) (x i) : ℂ)) * (S j).evalCyclic N x := by
    exact hweighted (S j) (by linarith) hr4 ((hSc j).mono (by dsimp [r]; linarith))
      (fun i => ψ (j i)) (fun i => (hψ (j i)).mono le_rfl (by dsimp [r]; linarith))
  choose g hE heval using hfamily
  let E := fun j => Classical.choice (hE j)
  let F := fun x : Fin 4 → ℤ => ∑ j, g j x
  have hcoeff : (∑ _j : Fin 4 → Fin n × ZMod L.period, ‖(1 : ℂ)‖) ≤ Real.exp r := by
    simpa using hcard
  have hEF : NativeIntegerExpansion (fun _ : Fin 4 => 1) 1 ((t + C) ^ C) F := by
    simpa only [F, one_mul] using
      ((NativeIntegerExpansion.weightedSum E (fun _ => 1) hr hcard hcoeff).mono hcost)
  have he (x : Fin 4 → ZMod N) : F (fun i => ((x i).val : ℤ)) =
      ∑ j, ((∏ i, ψ (j i) (x i)) : ℝ) * (S j).evalCyclic N x := by
    apply Finset.sum_congr rfl
    intro j _
    simpa only [Complex.ofReal_prod] using heval j x
  refine ⟨F, ⟨hEF⟩, ?_⟩
  simpa only [he] using herr

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra

theorem exists_antisymmetric_box_approximation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q b t r : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {V : NativeAntisymmetricOrbitFactors W N p}
      (R : NativeAntisymmetricFrozenDescent V q) (_L : NativeAntisymmetricLocalModels R b),
      0 ≤ t → 0 ≤ r → q ≤ t → b ≤ t → Real.exp ((t + r + C) ^ C) ≤ (N : ℝ) →
      ∃ F : (Fin 4 → ℤ) → ℂ,
        Nonempty (NativeIntegerExpansion (fun _ : Fin 4 => 1) 1 ((t + r + C) ^ C) F) ∧
        (𝔼 x : Fin 4 → ZMod N,
          ‖W.antisymmetricBoxValue V.leftIndex V.rightIndex (fun i => ((x i).val : ℤ)) -
            F (fun i => ((x i).val : ℤ))‖) ≤ Real.exp (-r) := by
  obtain ⟨A, _, hexpand⟩ := exists_antisymmetric_box_expansion 2
  let X : Polynomial ℕ := Polynomial.X
  let T := X + 100
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((T + Polynomial.C A) ^ A + 2 * T)
  refine ⟨C, hC, ?_⟩
  intro p q b t r W N _ V R L ht hr hqt hbt hN
  let u := t + r + 100
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hsum : (u + A) ^ A + 2 * u ≤ (t + r + C) ^ C := by
    simpa [T, X, u, Polynomial.eval₂_pow] using hbudget (t + r) (add_nonneg ht hr)
  have hcost : (u + A) ^ A ≤ (t + r + C) ^ C := by linarith
  have hscale : 2 * u ≤ (t + r + C) ^ C := by
    have : 0 ≤ (u + A) ^ A := by positivity
    linarith
  let ρ := Real.exp (-(2 * u))
  have hρ : 0 < ρ := Real.exp_pos _
  have hprec : 1 / ρ ≤ Real.exp ((u + 2) ^ 2) := by
    dsimp [ρ]
    rw [one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg u]
  obtain ⟨F, ⟨E⟩, herr⟩ := hexpand R L hu (hqt.trans (by dsimp [u]; linarith))
    (hbt.trans (by dsimp [u]; linarith)) hρ hprec
  have hrecip : 1 / (N : ℝ) ≤ ρ := by
    have hh := one_div_le_one_div_of_le (Real.exp_pos (2 * u))
      ((Real.exp_le_exp.mpr hscale).trans hN)
    simpa only [ρ, one_div, Real.exp_neg] using hh
  refine ⟨F, ⟨E.mono hcost⟩, herr.trans ?_⟩
  calc
    _ ≤ Real.exp (u + 73) * (2 * ρ) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.exp_nonneg _)
    _ = 2 * Real.exp (73 - u) := by
      dsimp [ρ]
      rw [← mul_assoc, mul_comm (Real.exp (u + 73)) 2, mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ 2 * (Real.exp (-r) / 2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply (Real.exp_le_exp.mpr (show 73 - u ≤ -r - 1 by dsimp [u]; linarith)).trans
      exact exp_sub_one_le_half_exp (-r)
    _ = _ := by ring

end Erdos3

end

end OAI
