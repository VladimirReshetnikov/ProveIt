import OAI.Combinatorics.Progressions.Estimates.MixedAnchorExpansion
import OAI.Combinatorics.Progressions.Geometry.MixedAntisymmetricBox

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_mixed_kernel_correlation (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 0 ≤ p →
      ∀ (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
        {N : ℕ} [NeZero N] (i j : Fin W.outputDim),
      Real.exp (-p) ≤ (boxPhaseMoment (n + 2) (fun x : Fin (n + 2) → ZMod N =>
        W.mixedAntisymmetric i j (fun k => ((x k).val : ℤ)))).re →
      Nonempty (NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) ((p + C) ^ C)
        Finset.univ (fun x : Fin (n + 2) → ZMod N => fun k => ((x k).val : ℤ))
        (fun x => W.mixedAntisymmetric i j (fun k => ((x k).val : ℤ)))) := by
  obtain ⟨A, _, hanchor⟩ := NativeMultidegreeNilcharacter.exists_mixed_anchor_expansion n
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + (X + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro p hp W N _ i j hbias
  let K := W.mixedAntisymmetric i j
  let Kc := fun x : Fin (n + 2) → ZMod N => K (fun k => ((x k).val : ℤ))
  obtain ⟨a, ha⟩ := exists_box_corner_anchor_correlation Kc
  obtain ⟨E⟩ := hanchor W i j (fun k => ((a k).val : ℤ))
  have hmap (x : Fin (n + 2) → ZMod N) : boxCornerAnchor Kc a x =
      boxCornerAnchor K (fun k => ((a k).val : ℤ)) (fun k => ((x k).val : ℤ)) :=
    boxCornerAnchor_map (fun z : ZMod N => (z.val : ℤ)) K a x
  have hcorr : Real.exp (-p) ≤ ‖𝔼 x : Fin (n + 2) → ZMod N,
      K (fun k => ((x k).val : ℤ)) *
        star (star (boxCornerAnchor K (fun k => ((a k).val : ℤ))
          (fun k => ((x k).val : ℤ))))‖ := by
    have h := hbias.trans ha
    simp_rw [hmap] at h
    simpa only [Kc, star_star] using h
  obtain ⟨S⟩ := NativeSampleCorrelation.exists_of_expansion E.conjugate hp hcorr
  have hcost : p + (p + A) ^ A ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨S.mono hcost⟩

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_sum_kernel_correlation (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
      {N : ℕ} [NeZero N] (f : ZMod N → ℂ), (∀ x, ‖f x‖ ≤ 1) →
      ∀ (i : Fin W.outputDim) (A : Fin (n + 2) → (Fin (n + 2) → ZMod N) → ℂ),
      (∀ j x, ‖A j x‖ ≤ 1) → (∀ j, MissesBoxCoordinate (A j) j) →
      Real.exp (-p) ≤ ‖𝔼 u : Fin n → ZMod N, 𝔼 m : ZMod N, 𝔼 h : ZMod N,
        f (m + h + ∑ j, u j) * star (W.eval i (mixedSlotInput (h.val : ℤ) m.val (fun j => (u j).val))) *
          ∏ j, A j (Fin.cons h (Fin.cons m u))‖ →
      ∃ j k : Fin W.outputDim,
        Nonempty (NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) ((p + C) ^ C)
          Finset.univ (fun x : Fin (n + 2) → ZMod N => fun l => ((x l).val : ℤ))
          (fun x => W.mixedAntisymmetric j k (fun l => ((x l).val : ℤ)))) := by
  obtain ⟨a, _, hbox⟩ := exists_mixed_sum_antisymmetric_box n
  obtain ⟨b, _, hkernel⟩ := exists_mixed_kernel_correlation n
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a
  let R := X + Q + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p W N _ f hf i A hA hmiss hcorr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + a) ^ a
  let r := p + q + 2
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hpr : p ≤ r := by dsimp only [r]; linarith
  have hqr : q ≤ r := by dsimp only [r]; linarith
  have hr : 0 ≤ r := hp.trans hpr
  obtain ⟨j, k, hmoment⟩ := hbox W f hf i A hA hmiss hcorr
  have hmono (x : Fin (n + 2) → ℤ) :
      (W.mono hpr).mixedAntisymmetric j k x = W.mixedAntisymmetric j k x := rfl
  have hinput : Real.exp (-r) ≤
      (boxPhaseMoment (n + 2) (fun x : Fin (n + 2) → ZMod N =>
        (W.mono hpr).mixedAntisymmetric j k (fun l => (x l).val))).re := by
    simpa only [hmono] using (Real.exp_le_exp.mpr (neg_le_neg hqr)).trans hmoment
  obtain ⟨S⟩ := hkernel hr (W.mono hpr) j k hinput
  have hcost : (r + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, Q, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨j, k, ⟨S.mono hcost⟩⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
