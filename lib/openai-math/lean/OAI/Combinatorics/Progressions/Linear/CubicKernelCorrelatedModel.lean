import OAI.Combinatorics.Progressions.Geometry.CubicBoxStepDrop

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_cubic_kernel_correlated_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 4 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) ((p + C) ^ C),
        ∃ V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) ((p + C) ^ C),
          V.dim ≤ 8 * M.dim ∧
          (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 2)) k x,
            V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 2) e).symm j)) =
              V.eval k x) ∧
          NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
            M.eval (fun k x => V.eval k (fun j => x j.1)) ∧
          NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
            M.cubicMixedDerivative V.cubicTrilinearTriple ∧
          ∃ out : Fin M.outputDim, ∃ χ : ZMod N → AddChar (ZMod N) ℂ,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤ ‖finiteFourierCoeff
              (fun n => multiplicativeDerivative f h n * star (M.evalCyclic N out (correlationInput h n))) (χ h)‖) ∧
            ∃ (branch : Bool) (i j : Fin V.outputDim × Fin V.outputDim),
              Nonempty (NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 ((p + C) ^ C)
                Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
                (fun z => V.cubicAntisymmetricPair i j (z 1).val (z 2).val
                  (cyclicBranchOffset (z 0) branch))) := by
  obtain ⟨a, _, hmodel⟩ := exists_cubic_antisymmetric_box
  obtain ⟨b, _, hcorrelate⟩ := exists_cubic_kernel_correlation
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hsum : q + (q + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (q + b) ^ b := by positivity
  have hqC : q ≤ (p + C) ^ C := by linarith only [hsum, hpow]
  have hbC : (q + b) ^ b ≤ (p + C) ^ C := by linarith only [hsum, hq]
  obtain ⟨H, hH, hHdense, M, V, hdim, hsymm, hdiag, E, out, χ, hcorr, branch, i, j, hbias⟩ :=
    hmodel hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  let shift : ℤ := -(if branch then (N : ℤ) else 0)
  have hbias' : Real.exp (-q) ≤ (finiteTripleBoxCorrelation (fun k h y : ZMod N =>
      V.cubicAntisymmetricPair i j h.val y.val ((k.val : ℤ) + shift))).re := by
    simpa only [shift, cyclicBranchOffset, sub_eq_add_neg] using hbias
  obtain ⟨W⟩ := hcorrelate hq V i j shift hbias'
  refine ⟨H, hH, ?_, M.mono hqC, V.mono hqC, ?_, hsymm, hdiag.mono hqC, E.mono hqC,
    out, χ, ?_, branch, i, j, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hHdense
  · change V.dim ≤ 8 * M.dim
    exact hdim
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)
  · have hW := W.mono hbC
    exact ⟨by simpa only [NativeMultidegreeNilcharacter.cubicAntisymmetricPair,
      NativeMultidegreeNilcharacter.mono_eval, cyclicBranchOffset, shift, sub_eq_add_neg] using hW⟩

end Erdos3

end

end OAI
