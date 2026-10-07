import OAI.Combinatorics.Progressions.Estimates.NativeMixedReflectionBridge

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_separated_family (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex s => 1) p),
      (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
        W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) = W.eval k x) →
      ∀ {G Ω : Type*} (H : Finset G), H.Nonempty →
      ∀ (S : G → Finset Ω), (∀ h ∈ H, (S h).Nonempty) →
      ∀ (sample : G → Ω → Fin (s + 1) → ℤ) (f : G → Ω → ℂ),
      (∀ h ∈ H, ∀ u ∈ S h, ‖f h u‖ ≤ 1) →
      ∀ (j : Fin W.outputDim) (A : Fin (s + 1) → (Fin (s + 1) → ℤ) → ℂ),
      (∀ i x, ‖A i x‖ ≤ 1) →
      (∀ i x y, (∀ l, l ≠ i → x l = y l) → A i x = A i y) →
      (∀ h ∈ H, Real.exp (-p) ≤ ‖𝔼 u ∈ S h, f h u * star (W.eval j
        (mixedReplicatedInput (sample h u 0) (fun _ : Fin s => ∑ l : Fin s, sample h u l.succ))) *
          ∏ i, A i (sample h u)‖) →
      ∃ (a : Equiv.Perm (Fin s) → Fin W.outputDim)
        (B : Fin (s + 1) → (Fin (s + 1) → ℤ) → ℂ),
        (∀ i x, ‖B i x‖ ≤ 1) ∧
        (∀ i x y, (∀ l, l ≠ i → x l = y l) → B i x = B i y) ∧
        ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (H.card : ℝ) ≤ (H'.card : ℝ) ∧
          ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
            ‖𝔼 u ∈ S h, f h u * star (mixedPermutationProduct W.eval a (sample h u)) *
              ∏ i, B i (sample h u)‖ := by
  obtain ⟨a, _, hexpand⟩ := exists_mixed_permutation_partition_expansion s hs
  obtain ⟨b, _, htransfer⟩ := exists_separated_family_correlation s
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Q + 2 + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p W hsym G Ω H hH S hS sample f hf j A hA hAind hcorr
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + a) ^ a
  let r := p + q + 2
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hpr : p ≤ r := by dsimp only [r]; linarith
  have hqr : q ≤ r := by dsimp only [r]; linarith
  have E : NativeIntegerVectorEquivalence s q
      (fun i (x : Fin (s + 1) → ℤ) => W.eval i
        (mixedReplicatedInput (x 0) (fun _ : Fin s => ∑ l : Fin s, x l.succ)))
      (mixedAssignmentPartitionVector W.eval) := hexpand W hsym
  obtain ⟨k, B, hB, hBind, H', hsub, hH', hsize, hBcorr⟩ := htransfer hr (E.mono hqr)
    (mixedAssignmentPartitionVector_unit W.eval W.unit_eval) H hH S hS sample f hf j A hA hAind
    (fun h hh => (Real.exp_le_exp.mpr (neg_le_neg hpr)).trans (hcorr h hh))
  obtain ⟨D, hD, hDind, hDprod⟩ := W.exists_mixed_missing_factors (fun v => k (Sum.inr v))
  have hcost : (r + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, Q, q, r, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨(fun e => k (Sum.inl e)), (fun i x => B i x * star (D i x)),
    ?_, ?_, H', hsub, hH', ?_, ?_⟩
  · intro i x
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hB i x)).trans (hD i x)
  · intro i x y hxy
    change B i x * star (D i x) = B i y * star (D i y)
    rw [hBind i x y hxy, hDind i x y hxy]
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcost))
      (Nat.cast_nonneg _)).trans hsize
  · intro h hh
    simp only [Finset.prod_mul_distrib, ← star_prod, hDprod]
    simpa only [mixedAssignmentPartitionVector, star_mul, mul_comm, mul_left_comm, mul_assoc] using
      (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans (hBcorr h hh)

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
