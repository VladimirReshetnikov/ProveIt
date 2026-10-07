import OAI.Combinatorics.Progressions.Estimates.QuadraticCyclicAntisymmetric

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_antisymmetric_box :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) ((p + C) ^ C),
          ∃ i : Fin M.outputDim,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                star (M.evalCyclic N i (correlationInput h n))‖) ∧
            ∃ i' j' : Fin M.outputDim,
              Real.exp (-((p + C) ^ C)) ≤
                (finiteBoxCorrelation (fun x y : ZMod N =>
                  star (M.evalCyclic N i' (correlationInput x y)) *
                    M.evalCyclic N j' (correlationInput y x))).re := by
  obtain ⟨A, _, hanti⟩ := exists_quadratic_cyclic_antisymmetric
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (4 * Q)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcost : 4 * q ≤ (p + C) ^ C := by
    simpa [Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  obtain ⟨H, hH, hdense, M, i, hcorr, i', j', a, b, ha, hb, hpair⟩ := hanti hp f hf hG
  let K (x y : ZMod N) :=
    star (M.evalCyclic N i' (correlationInput x y)) * M.evalCyclic N j' (correlationInput y x)
  have hbox : Real.exp (-q) ^ 4 ≤ (finiteBoxCorrelation K).re :=
    (pow_le_pow_left₀ (Real.exp_nonneg _) hpair 4).trans
      (norm_weighted_pair_mean_pow_four_le_box K a b ha hb)
  have hpower : Real.exp (-q) ^ 4 = Real.exp (-(4 * q)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  rw [hpower] at hbox
  refine ⟨H, hH, ?_, M.mono hqC, i, ?_, i', j', ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)
  · exact (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans hbox

end Erdos3

end

end OAI
