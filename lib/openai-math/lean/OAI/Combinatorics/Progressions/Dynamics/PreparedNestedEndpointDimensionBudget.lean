import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteForwardFixedCenterThreshold
import OAI.Combinatorics.Progressions.Estimates.PreparedUniformEarlyRadiusWithCutoff

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

private theorem exists_endpointDimension_local_budget (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {x pnum : ℝ}, 0 ≤ x → pnum ∈ Set.Icc 0 x →
      ∀ nX M : ℕ, (nX : ℝ) ≤ x → (M : ℝ) ≤ x →
      allocatedComparisonDimension m pnum ≤ (x + C) ^ C ∧
        ((nX + m * M : ℕ) : ℝ) ≤ (x + C) ^ C := by
  let Q : Polynomial ℕ := allocatedComparisonDimension m Polynomial.X +
    Polynomial.C (m + 1) * Polynomial.X
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro x pnum hx hnum nX M hnX hM
  have htotal : allocatedComparisonDimension m x + (m + 1 : ℕ) * x ≤ (x + C) ^ C := by
    simpa [Q, allocatedComparisonDimension, Polynomial.eval₂_pow] using hbound x hx
  have hdim0 : 0 ≤ allocatedComparisonDimension m x := (allocatedComparisonDimension_bounds m hx).1
  have hmul0 : (0 : ℝ) ≤ (m + 1 : ℕ) * x := mul_nonneg (Nat.cast_nonneg _) hx
  have hmod : ((nX + m * M : ℕ) : ℝ) ≤ (m + 1 : ℕ) * x := by
    have hmul := mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    nlinarith only [hnX, hmul]
  exact ⟨(allocatedComparisonDimension_mono m hnum.1 hnum.2).trans
    (by linarith only [htotal, hmul0]), hmod.trans (by linarith only [htotal, hdim0])⟩

private theorem exists_endpointDimension_uniform_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ m : ℕ, m ≤ s →
      ∀ {x pnum : ℝ}, 0 ≤ x → pnum ∈ Set.Icc 0 x →
      ∀ nX M : ℕ, (nX : ℝ) ≤ x → (M : ℝ) ≤ x →
      allocatedComparisonDimension m pnum ≤ (x + C) ^ C ∧
        ((nX + m * M : ℕ) : ℝ) ≤ (x + C) ^ C := by
  classical
  choose ex hex hb using fun j : Fin (s + 1) => exists_endpointDimension_local_budget j.val
  let C := 2 + ∑ j, ex j
  refine ⟨C, by dsimp only [C]; omega, ?_⟩
  intro m hm x pnum hx hnum nX M hnX hM
  let j : Fin (s + 1) := ⟨m, by omega⟩
  have hsum : ex j ≤ ∑ i, ex i :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have heC : ex j ≤ C := by dsimp only [C]; omega
  have hCReal : (2 : ℝ) ≤ C := Nat.cast_le.mpr ((hex j).trans heC)
  have hpow : (x + ex j) ^ ex j ≤ (x + C) ^ C :=
    (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl (Nat.cast_le.mpr heC)) _).trans
      (pow_le_pow_right₀ (by linarith only [hx, hCReal]) heC)
  have h := hb j hx hnum nX M hnX hM
  exact ⟨h.1.trans hpow, h.2.trans hpow⟩

noncomputable def preparedNestedEndpointDimensionExponent (s : ℕ) : ℕ :=
  (exists_endpointDimension_uniform_budget s).choose

theorem preparedNestedEndpointDimensionExponent_two_le (s : ℕ) :
    2 ≤ preparedNestedEndpointDimensionExponent s :=
  (exists_endpointDimension_uniform_budget s).choose_spec.1

theorem preparedNestedEndpointDimension_bounds
    (s m : ℕ) (hm : m ≤ s) (A : ℕ) (constants : ℕ → ℕ)
    (innerDepth outer inner : ℕ) {Bstruct pnum : ℝ}
    (hA : preparedNestedEndpointDimensionExponent s ≤ A)
    (houter : 1 ≤ outer) (hB : 0 ≤ Bstruct) (hnum : pnum ∈ Set.Icc 0 Bstruct)
    (nX M : ℕ) (hnX : (nX : ℝ) ≤ Bstruct) (hM : (M : ℝ) ≤ Bstruct) :
    allocatedComparisonDimension m pnum ≤ preparedFiniteForwardParameter A constants inner
      (candidateNestedForwardSeed A constants innerDepth outer Bstruct) ∧
    ((nX + m * M : ℕ) : ℝ) ≤ preparedFiniteForwardParameter A constants inner
      (candidateNestedForwardSeed A constants innerDepth outer Bstruct) := by
  have hAtwo := (preparedNestedEndpointDimensionExponent_two_le s).trans hA
  have hlocal := (exists_endpointDimension_uniform_budget s).choose_spec.2 m hm
    hB hnum nX M hnX hM
  have hwork := preparedFiniteForward_shiftedPower_le_work A
    (preparedNestedEndpointDimensionExponent s) constants innerDepth hAtwo hA hB
  have hseed : preparedFiniteForwardWork A constants innerDepth Bstruct ≤
      candidateNestedForwardSeed A constants innerDepth outer Bstruct := by
    simpa only [candidateNestedForwardSeed_succ, candidateNestedForwardSeed_zero] using
      candidateNestedForwardSeed_monotone A constants innerDepth hAtwo hB houter
  have hparameter := le_preparedFiniteForwardParameter A constants inner
    (candidateNestedForwardSeed_nonneg A constants innerDepth outer hB)
  exact ⟨hlocal.1.trans (hwork.trans (hseed.trans hparameter)),
    hlocal.2.trans (hwork.trans (hseed.trans hparameter))⟩

end Erdos3.VectorPolynomial

end

end OAI
